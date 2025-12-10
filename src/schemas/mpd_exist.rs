use rand::rngs::OsRng;
use rand_core::{ CryptoRng, RngCore, CryptoRngCore };   
use std::time::{ Instant, Duration }; 
use curve25519_dalek::{ scalar::Scalar, RistrettoPoint, traits::Identity};
use zeroize::Zeroize;
use crate::usefulstructs::*;
use crate::usefulfuncs::{random_ecg, random_ristretto_point, random_scalar, chal_single_proof_square, chal_distance, random_vec_scalar, lincomb_pow2, two_pow, scalar_to_bits, compute_mpd_with_window_scalar, chal_list};

use crate::commit::*;

// --------- MPD Exist ---- //
pub fn proof_exist_bin<T: CryptoRng + RngCore>(
    set: &Set,
    l: usize,                  // length in bits
    a: usize,                  // length of matrix profile
    m_i: &[RistrettoPoint],    // Pedersen commitments of MPD_i bits
    d_ij: &[&[RistrettoPoint]],   // Pedersen commitments of distances s_i and s_j (flattened: a * l)
    z_i: &[Scalar],            // openings for m_i
    w_ij: &[&[Scalar]],           // openings for d_ij (flattened: a * l)
    rng_proof: &mut T,
) -> ProofExistij {
    // --- Basic sanity checks ---
    debug_assert_eq!(m_i.len(), l, "m_i must have length l");
    debug_assert_eq!(z_i.len(), l, "z_i must have length l");
    debug_assert_eq!(d_ij.len(), a, "d_ij must have length a * l");
    debug_assert_eq!(w_ij.len(), a, "w_ij must have length a * l");

    let h = set.h_;

    let mut r_i: Vec<RistrettoPoint> = Vec::with_capacity(a * l);
    let mut res_i: Vec<Scalar>       = Vec::with_capacity(a * l);
    let mut c_i: Vec<Scalar>         = Vec::with_capacity(a);
    let mut y_i: Vec<RistrettoPoint> = Vec::with_capacity(a * l);

    let mut c_accum = Scalar::ZERO;
    let mut alea_buffer: Vec<Scalar> = Vec::with_capacity(l);

    // --- 1. Find index j* such that m_i[u] - d_ij[j*l + u] = h * (z_i[u] - w_ij[j*l + u]) for all u ---
    let mut index_j_star: Option<usize> = None;

    'outer: for j in 0..a {
        let mut is_j = true;

        for u in 0..l {
            let alpha_u = z_i[u] - w_ij[j][u];
            let y_u     = m_i[u] - d_ij[j][u];

            if y_u != h * alpha_u {
                is_j = false;
                break;
            }
        }

        if is_j {
            index_j_star = Some(j);
            break 'outer;
        }
    }

    let index_j_star = index_j_star.expect("No valid j* found for the given commitments.");

    // --- 2. Build real transcript for j* and simulated ones for j != j* ---
    for j in 0..a {
        if j == index_j_star {
            // Real proof branch
            for u in 0..l {
                // let alpha_u = z_i[u] - w_ij[j][u];
                let y_u     = m_i[u] - d_ij[j][u];

                y_i.push(y_u);

                let r = random_scalar(rng_proof);
                alea_buffer.push(r);                 // stored for later to finalize z responses

                let r_ju = h * r;                    // commitment for the honest branch
                r_i.push(r_ju);

                // Placeholder for z; will be overwritten after computing the global challenge
                res_i.push(Scalar::ZERO);
            }

            // Challenge for j* is determined later from Fiat–Shamir: set to 0 for now
            c_i.push(Scalar::ZERO);
        } else {
            // Simulated branches
            let c_j = random_scalar(rng_proof);
            c_i.push(c_j);
            c_accum += c_j;

            for u in 0..l {
                // let alpha_u = z_i[u] - w_ij[j][u];
                let y_u     = m_i[u] - d_ij[j][u];

                y_i.push(y_u);

                // Simulated response
                let res_ju = random_scalar(rng_proof);
                res_i.push(res_ju);

                // r_i = h * res_ju - c_j * y_u  (Sigma-protocol style simulation)
                let r_iu = h * res_ju - c_j * y_u;
                r_i.push(r_iu);
            }
        }
    }

    // --- 3. Compute global challenge and derive c_{j*} ---
    // g_list = [h, h, ..., h] with length a*l
    let g_list: Vec<RistrettoPoint> = vec![h; a * l];

    let c = chal_list(&r_i, &y_i, &g_list);
    let c_j_star = c - c_accum;

    // set challenge for the real branch
    c_i[index_j_star] = c_j_star;

    // --- 4. Finalize real responses z for j* ---
    for u in 0..l {
        let alpha_u      = z_i[u] - w_ij[index_j_star][u];
        let res_j_star_u = alea_buffer[u] + alpha_u * c_j_star;
        res_i[index_j_star * l + u] = res_j_star_u;
    }
    return ProofExistij{r_i: r_i, c_i: c_i, z_i:res_i}
}

pub fn verify_exist_bin(
    m_i: &[RistrettoPoint],
    d_ij: &[&[RistrettoPoint]],
    l: usize, // length of bits
    a: usize, // length of m_i
    set: &Set,
    proofs_exist: &ProofExistij
) -> bool {
    let mut res = true;
    let h = set.h_;
    let mut y_i : Vec<RistrettoPoint> = Vec::with_capacity(a*l);
    let mut g_i : Vec<RistrettoPoint> = Vec::with_capacity(a*l);
    for j in 0..a{
        for u in 0..l{
            let y_u = m_i[u] - d_ij[j][u];
            y_i.push(y_u);
            g_i.push(h);
            let r_i = proofs_exist.r_i[j*l+u];
            let c_i = proofs_exist.c_i[j];
            let z_i = proofs_exist.z_i[j*l+u];
            res &= h * z_i == r_i + y_u*c_i;
        }
    }
    // verify c
    let c = chal_list(&proofs_exist.r_i, &y_i, &g_i);
    let mut c_to_test : Scalar = Scalar::ZERO;
    for c_i in proofs_exist.c_i.clone(){
        c_to_test += c_i;
    }
    res &= c_to_test == c;
    y_i.zeroize();
	g_i.zeroize();
    res
}

pub fn measure_time_exist_bin(
    upper: usize,
    n: usize,
    m: usize,
    u: usize,
    iter: usize,
) {
    let a = n - m + 1; // number of MPD entries

    let mut time_setup      = Duration::ZERO;
    let mut time_commit     = Duration::ZERO;
    let mut time_proof_mpd  = Duration::ZERO;
    let mut time_verify_mpd = Duration::ZERO;

    for _ in 0..iter {
        let mut rng        = OsRng;
        let mut rng_k      = OsRng;
        let mut rng_proof  = OsRng;
        // let mut rng_dist   = OsRng;

        let ts = random_ecg(&mut rng, n, upper); 

        // --- Setup ---
        let t0 = Instant::now();
        let mut set = setup(n, &mut rng);
        time_setup += t0.elapsed();

        // --- Commit (kept for parity) ---
        let t1 = Instant::now();
        let commitment = commit(&mut set, &ts.to_vec(), &mut rng_k);

        // let x = &commitment.x_;
        // let k = &commitment.k_;
        let n = set.n_;
        let g = set.gen;
        let h = set.h_;

        // calculate commit
        let (_, _, x_diff, k_diff, k_tilde) = calculate_inner_diff_commit(&commitment, &set, &mut rng_proof);
        
        let (d_vec, _, w, _, _) = calculate_dist_commit(&mut rng_proof, n, m, u, g, h, &x_diff, &k_diff, &k_tilde);

        // MPD
        let mpd      = compute_mpd_with_window_scalar(&ts, m);
        let mpd_bin: Vec<Vec<Scalar>> = mpd.iter().map(|x| scalar_to_bits(x, u)).collect();

        let (m_vec, _, z_vec) = calculate_mpd_commit(&g, &h, mpd_bin, u, &mut rng_proof);

        let m_vec_refs: Vec<&[RistrettoPoint]> = m_vec.iter().map(|inner| inner.as_slice()).collect();
        let z_vec_refs: Vec<&[Scalar]> = z_vec.iter().map(|inner| inner.as_slice()).collect();
        let d_vec_refs: Vec<&[RistrettoPoint]> = d_vec.iter().map(|inner| inner.as_slice()).collect();
        let w_refs : Vec<&[Scalar]> = w.iter().map(|inner| inner.as_slice()).collect();

        let tak = t1.elapsed();
        time_commit += tak;
        println!("Commit time {:?}", tak);

        // Proof
        let mut time_proof_iter  = Duration::ZERO;
        let mut time_verify_iter = Duration::ZERO;
        let mut res = true;
        for i in 0..a{
            let m_i = m_vec_refs[i];
            let d_ij = &d_vec_refs[i*a .. i*a + a];
            let zi_pub = z_vec_refs[i];
            let w_ij = &w_refs[i*a .. i*a+a];

            let t_proof = Instant::now();
            let proof_existence = proof_exist_bin(
                &set,
                u,     
                a,
                &m_i,
                d_ij,
                &zi_pub,
                w_ij,
                &mut rng_proof
            );

            time_proof_iter += t_proof.elapsed();

            // --- Verify ---
            let t_verify = Instant::now();
            res &= verify_exist_bin(&m_i, d_ij, u, a, &set, &proof_existence);
            time_verify_iter += t_verify.elapsed(); 
        }
        println!("{:?}", res);
        debug_assert!(res, "verify_exist_bin failed ");

        time_proof_mpd  += time_proof_iter;
        println!("Proof time: {:?}", time_proof_iter);
        time_verify_mpd += time_verify_iter;
        println!("Verify time: {:?}", time_verify_iter);
    }

    println!("Total over {} iterations:", iter);
    println!("  setup:        {:?}", time_setup/(iter as u32));
    println!("  commit:       {:?}", time_commit/(iter as u32));
    println!("  proof (MPD):  {:?}", time_proof_mpd/(iter as u32));
    println!("  verify (MPD): {:?}", time_verify_mpd/(iter as u32));
}