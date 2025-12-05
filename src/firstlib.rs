#[allow(unused_imports)]
#[allow(unused_variables)]
use rand::rngs::OsRng;
use rand_core::{ CryptoRng, RngCore, CryptoRngCore };   
use std::time::{ Instant, Duration }; 
use curve25519_dalek::{ scalar::Scalar, RistrettoPoint, traits::Identity};
use zeroize::Zeroize;
use crate::usefulstructs::*;
use crate::usefulfuncs::{random_ecg, random_ristretto_point, random_scalar, chal_single_proof_square, chal_distance, random_vec_scalar, lincomb_pow2, two_pow, scalar_to_bits, compute_mpd_with_window_scalar, chal_list};
// TODO: Write functions to calculate new commitements, like M and D from commitment ts

// Generate a setup set:
pub fn setup<T: CryptoRng + RngCore>(n: usize, rng: &mut T) -> Set {
    let generator = random_ristretto_point(rng);
    let h = random_ristretto_point(rng);
    let set = Set{gen: generator, h_: h, n_: n};  
    return set;   
}

// Generate a commitment:
pub fn commit<T: CryptoRng + RngCore>(
    s: &mut Set,
    time_series: &Vec<Scalar>, 
    rng_k: &mut T
) -> Commit {
    let gen = s.gen;
    let h = s.h_;

    let mut k: Vec<Scalar> = Vec::new();
    let mut c: Vec<RistrettoPoint> = Vec::new();
    let mut x_s: Vec<Scalar> = Vec::new();

    for i in time_series {
        let k_i = random_scalar(rng_k);
        let c_i = i*gen + &k_i*h;
        c.push(c_i);
        k.push(k_i);
        x_s.push(*i);
    }
    let commit = Commit{k_: k, x_: x_s, c_: c};
    return commit;
}

// Open a commitment:
pub fn open(c: &Commit) -> &Vec<Scalar>{
    let res = &c.x_;
    return res;
}

// ------ Proof of square of distance for subsequences si and sj ------
// The proof takes the secret x_ij, the private key k_ij, k_ij_tilde the public key c_ij, c_ij_tilde 
pub fn proof_square_ij<T: CryptoRng + RngCore>(
    x_ij: Scalar,
    k_ij: Scalar,
    c_ij: &RistrettoPoint,
    c_ij_tilde: &RistrettoPoint,
    k_ij_tilde: Scalar,
    set: &Set,
    rng_proof: &mut T,
) -> ProofSquareij {
    // generators
    let g = set.gen;
    let h = set.h_;

    // randomness
    let s1 = random_scalar(rng_proof);
    let s2 = random_scalar(rng_proof);
    let r = random_scalar(rng_proof);

    // public elements
    let rr1 = r * g;
    let rr2 = r * c_ij;
    let s1_pub = s1 * h;
    let s2_pub = s2 * h;

    // challenge
    let c_chal = chal_single_proof_square(&rr1, &rr2, &s1_pub, &s2_pub, &c_ij, &c_ij_tilde, &g, &h);

    // responses
    let u  = r  + x_ij   * c_chal;
    let v1 = s1 + k_ij   * c_chal;
    let v2 = s2 + k_ij_tilde * c_chal;

    let proof = ProofSquareij {
        r_1: rr1,
        r_2: rr2,
        s_1: s1_pub,
        s_2: s2_pub,
        u: u,
        v1: v1,
        v2: v2
    };

    return proof
}

// ------ verify proof square ij ------
// calculate the challenge from the elements in the proof, and verify pi_square_i_j
pub fn verify_square_ij(
    i: usize,
    j: usize, 
    c_ij: &RistrettoPoint,
    c_ij_tilde: &RistrettoPoint,
    set: &Set, 
    proof_square_ij: &ProofSquareij
)-> bool{
    let g = set.gen;
    let h = set.h_;
    let r1 = &proof_square_ij.r_1;
    let r2 = &proof_square_ij.r_2;
    let s1 = &proof_square_ij.s_1;
    let s2 = &proof_square_ij.s_2;
    let u = &proof_square_ij.u;
    let v1 = &proof_square_ij.v1;
    let v2 = &proof_square_ij.v2;

    let c_verify = chal_single_proof_square(&r1, &r2, &s1, &s2, &c_ij, &c_ij_tilde, &g, &h);

    if (u*g+v1*h != r1+s1+c_verify*c_ij) || (u*c_ij+v2*h != r2+s2+c_verify*c_ij_tilde) {
    	return false;
    } 
    return true;
}

pub fn proof_square<T: CryptoRng + RngCore>(
    commitement: &Commit,
    set: &Set,
    n: usize,
    m: usize,
    x_diff: &[Scalar],
    k_diff: &[Scalar],
    c_diff: &[RistrettoPoint],
    c_tilde: &[RistrettoPoint],
    k_tilde: &[Scalar],           
    rng_proof: &mut T,
) -> Vec<Option<ProofSquareij>> {
    let mut proofs:   Vec<Option<ProofSquareij>>  = Vec::with_capacity(n * n);

    for i in 0..n {
        for j in 0..n{
            if i.abs_diff(j) <= m/2 || j<i { // symetric and ignore the self-join window around i
                proofs.push(None);
                continue; 
            } 
            let p_ij = proof_square_ij(
                x_diff[i*n+j], 
                k_diff[i*n+j], 
                &c_diff[i*n+j], 
                &c_tilde[i*n+j], 
                k_tilde[i * n + j], 
                &set, 
                rng_proof
            );
            proofs.push(Some(p_ij));
        }
    }
    proofs
}

pub fn verify_square(
    n: usize,
    c_ij_vec: &[RistrettoPoint],
    c_tilde_vec: &[RistrettoPoint], 
    set: &Set,
    proofs: &[Option<ProofSquareij>], 
) -> bool {
    let mut res: bool = true;
    for i in 0..n {
        for j in 0..n {
            let idx = i * n + j;
            match (&c_tilde_vec[idx], &c_ij_vec[idx], &proofs[idx]) {
                (c_ij_tilde, c_ij, Some(pij)) => {
                    let ok = verify_square_ij(
                        i,
                        j, 
                        &c_ij,
                        &c_ij_tilde,
                        &set, 
                        &pij
                    );
                    res &= ok;
                }
                _ => { continue; }
            }
        }
    }

    res
}

pub fn calculate_inner_diff_commit<T: CryptoRng + RngCore>(
    commitment: &Commit,
    set: &Set,
    rng: &mut T
)->(Vec<RistrettoPoint>,Vec<RistrettoPoint>,Vec<Scalar>,Vec<Scalar>,Vec<Scalar>){

    let c_pub = &commitment.c_;
    let k = &commitment.k_;
    let x = &commitment.x_;

    // let g = set.gen;
    let h = set.h_;

    let n = set.n_;

    let mut c_diff: Vec<RistrettoPoint> = Vec::with_capacity(n*n);
    let mut c_tilde : Vec<RistrettoPoint> = Vec::with_capacity(n*n);
    let mut x_diff: Vec<Scalar> = Vec::with_capacity(n*n);
    let mut k_diff: Vec<Scalar> = Vec::with_capacity(n*n);
    let k_tilde = random_vec_scalar(rng, n*n);
    
    for i in 0..n{
        for j in 0..n{
            let c_ij = c_pub[i] - c_pub[j];
            let x_ij = x[i] - x[j];
            let k_ij = k[i] - k[j];
            let k_ij_tilde = k_tilde[i*n+j];
            let c_ij_tilde = x_ij * c_ij + k_ij_tilde * h;

            c_tilde.push(c_ij_tilde);
            x_diff.push(x_ij);
            k_diff.push(k_ij);
            c_diff.push(c_ij);
        }
    }
    (c_diff, c_tilde, x_diff, k_diff, k_tilde)

}

pub fn calculate_dist_commit<T: CryptoRng + RngCore>(
    rng_proof: &mut T,
    n: usize,
    m: usize,
    u: usize,
    g: RistrettoPoint,
    h: RistrettoPoint,
    x_diff: &[Scalar],
    k_diff: &[Scalar],
    k_tilde: &[Scalar],
)->(Vec<Vec<RistrettoPoint>>, Vec<Vec<RistrettoPoint>>, Vec<Vec<Scalar>>, Vec<Vec<Scalar>>){
    // number of subsequences
    let l = n - m + 1;
        
    let mut c_vec : Vec<Vec<RistrettoPoint>> = Vec::with_capacity(l*l);
    let mut c_bis_vec : Vec<Vec<RistrettoPoint>> = Vec::with_capacity(l*l);
    let mut d_private_bin_vec: Vec<Vec<Scalar>> = Vec::with_capacity(l*l);
    let mut w : Vec<Vec<Scalar>> = Vec::with_capacity(l*l);

    for i in 0..l{
        for j in 0..l{
            let mut wij = Scalar::ZERO;
            let mut dij = Scalar::ZERO; // compute only once, never used after in other proofs

            // accumulate over window m
            for r in 0..m {
                let xij = x_diff[(i + r) * n + (j + r)]; // x[i + r] - x[j + r];
                let kij = k_diff[(i + r) * n + (j + r)]; // k[i + r] - k[j + r];
                let k_tilde_ij = k_tilde[(i + r) * n + (j + r)];
                wij += xij * kij + k_tilde_ij;
                dij += xij * xij;
            }
            let dij_bin = scalar_to_bits(&dij, u);

            // sample u-1 random public shares for wij and set the last to match sum
            let mut wij_pub: Vec<Scalar> = Vec::with_capacity(u);
            for _ in 0..(u - 1) {
                wij_pub.push(random_scalar(rng_proof));
            }
            let first = lincomb_pow2(&wij_pub);
            let denom = two_pow(u - 1); // 2^(u-1)
            let last = (wij - first) * denom.invert(); // division with scalar
            wij_pub.push(last);

            let d_ij_vec: Vec<RistrettoPoint> = dij_bin.iter().zip(wij_pub.iter()).map(|(dij, wij)| dij * g + wij * h).collect();
            let d_ij_bis_vec: Vec<RistrettoPoint> = d_ij_vec.iter().map(|d_ij| d_ij - g).collect();
            
            d_private_bin_vec.push(dij_bin);
            c_vec.push(d_ij_vec);
            c_bis_vec.push(d_ij_bis_vec);
            w.push(wij_pub); // push the wiju list
        }
    }
    return (c_vec, c_bis_vec, w, d_private_bin_vec) // (D_iju), (D_iju/g), (w_iju), (d_iju)
}

pub fn measure_time_proof_square(
    upper: usize,
    n: usize,
    m: usize, 
    iter: usize
){
    let mut time_setup = Duration::ZERO;
    let mut time_commit = Duration::ZERO;
    let mut time_p_square = Duration::ZERO;
    let mut time_verify_p_square = Duration::ZERO;

    for _i in 0..iter {
        
        let mut rng = OsRng; 
        let mut rng_k = OsRng;
        let mut rng_proof_square = OsRng;
        // Setup:
        let start_setup = Instant::now();
        let mut set: Set = setup(n, &mut rng);
        let duration_setup = start_setup.elapsed();
        time_setup = time_setup + duration_setup;

        let ts = random_ecg(&mut rng, n, upper);

        // Commit:
        let start_commit = Instant::now();
        // ----------- General commit -------------- //
        let c: Commit = commit(&mut set, &ts, &mut rng_k); // commit of device

        let (c_diff, c_tilde, x_diff, k_diff, k_tilde) = calculate_inner_diff_commit(&c, &set, &mut rng);

        let duration_commit = start_commit.elapsed();
        time_commit = time_commit + duration_commit;

        // Proof square :
        let start_proof = Instant::now();
        let p_square = proof_square(
            &c, 
            &set,
            n,
            m,
            &x_diff,
            &k_diff,
            &c_diff,
            &c_tilde, 
            &k_tilde, 
            &mut rng_proof_square
        );

        let duration_proof = start_proof.elapsed();
        time_p_square += duration_proof;
        
        // Verify proof of square :
        let start_verify = Instant::now();
        let res = verify_square(
            n, 
            &c_diff, 
            &c_tilde, 
            &set, 
            &p_square
        );
        let duration_verify = start_verify.elapsed();
        time_verify_p_square = time_verify_p_square + duration_verify;

        println!("Verify: {}", res);
        debug_assert!(res, "square proof failed verification"); 
    }
    let average_time_setup = time_setup / (iter as u32);
    let average_time_commit = time_commit / (iter as u32);
    let average_time_proof = time_p_square / (iter as u32);
    let average_time_verify = time_verify_p_square / (iter as u32);
        
        
    println!("Average with n= {}, m = {}", n, m);
    print!("Setup: {:?} \n", average_time_setup);
    print!("Commit: {:?} \n", average_time_commit);
    print!("Proof: {:?} \n", average_time_proof);
    print!("Verify: {:?} \n", average_time_verify);
}
    

// ------------------- Proof distance ---------------------------
// Zero knowledge proof to prove that the distances have been correctely commited without revealing the values
// OR Proof: Y_1 = g^alpha or Y_2 = g^alpha
// If Y_1 = g^alpha: 
//      // simulate Y_2 = g^alpha
//      z_2, c_2 <- random;
//      r_2 = z_2 * g - c_2 * Y_2;
//      // prove Y_1 = g^alpha
//      r <- random;
//      r_1 = g^r;
//      c <- Hash(Y_1, Y_2, r_1, r_2, g);
//      c_1 = c xor c_2;
//      z_1 <- r + alpha*c_1
//      return {r_1, r_2, c_1, c_2, z_1, z_2}

pub fn proof_distance_bin_iju<T: CryptoRng + RngCore>(
    c_iju: &RistrettoPoint,      // Y_1  
    c_iju_bis: &RistrettoPoint,  // Y_2
    wiju: Scalar,          // alpha
    set: &Set,
    rng_proof: &mut T,
) -> ProofDistanceiju {
    // let g = set.gen;       // RistrettoPoint
    let h = set.h_;        // RistrettoPoint

    // Commitment for this bit
    let r1: RistrettoPoint;
    let r2: RistrettoPoint;
    let c1: Scalar;
    let c2: Scalar;
    let z1: Scalar;
    let z2: Scalar;
    let c_chal: Scalar; 

    // verify which condition 
    if *c_iju == wiju * h {
        let r = random_scalar(rng_proof);   
        r1 = h * r;  
        z2 = random_scalar(rng_proof);
        c2 = random_scalar(rng_proof);
        r2 = z2 * h - c2 * c_iju_bis;
        c_chal = chal_distance(&r1, &r2, &h, &c_iju, &c_iju_bis);
        c1 = c_chal - c2;
        z1 = r + c1 * wiju;
    }
    else{
        let r_ = random_scalar(rng_proof);   
        r2 = h * r_;  
        z1 = random_scalar(rng_proof);
        c1 = random_scalar(rng_proof);
        r1 = z1 * h - c1 * c_iju;
        c_chal = chal_distance(&r1, &r2, &h, &c_iju, &c_iju_bis);
        c2 = c_chal - c1;
        z2 = r_ + c2 * wiju;
    }         

    ProofDistanceiju { r_1: r1, r_2: r2, c_1: c1, c_2: c2, response_1: z1, response_2: z2 }
}

// return vector of proofs for each u, for a given i,j
pub fn proof_distance_bin_ij<T: CryptoRng + RngCore>(
    set: &Set,
    c_ij: &[RistrettoPoint],
    c_ij_bis: &[RistrettoPoint],
    w_ij: &[Scalar],
    u: usize,
    rng_proof_distance: &mut T,
) -> Vec<ProofDistanceiju> {
    // per-bit proofs
    let mut proof_distance: Vec<ProofDistanceiju> = Vec::with_capacity(u);

    for bit in 0..u {
        // per-bit proof of knowledge of wij_pub[bit] in C_u
        let proof = proof_distance_bin_iju(&c_ij[bit], &c_ij_bis[bit], w_ij[bit], &set, rng_proof_distance);
        proof_distance.push(proof);
    }
    proof_distance
}

pub fn verify_distance_bin_ij(
    c_ij: &[RistrettoPoint],
    c_ij_bis: &[RistrettoPoint],          
    set: &Set,
    proofs: &[ProofDistanceiju],
) -> bool {
    let u = proofs.len();

    // let g = set.gen;
    let h = set.h_;

    for idx in 0..u {
        let res_1 = proofs[idx].response_1; //z1
        let res_2 = proofs[idx].response_2; //z2
        let r1  = proofs[idx].r_1; // R1
        let r2  = proofs[idx].r_2; // R2
        let c1  = proofs[idx].c_1; // c1
        let c2  = proofs[idx].c_2; // c2
        let c_u = c_ij[idx]; // Y1
        let c_u_bis = c_ij_bis[idx]; // Y2

        // Recompute challenge
        let c = chal_distance(&r1, &r2, &h, &c_u, &c_u_bis);

        if (res_1 * h - c1 * c_u != r1) || (res_2 * h - c2 * c_u_bis != r2) || (c != c1 + c2)  {
            return false;
        }
    }
    true
}

// ---------------------------------------
// Proof over all pairs of i and j
// ---------------------------------------
pub fn proof_distance<T: CryptoRng + RngCore>(
    n: usize,
    m: usize,
    u: usize,
    set: &Set,
    c_vec : &[&[RistrettoPoint]],
    c_bis_vec : &[&[RistrettoPoint]],
    w : &[&[Scalar]],
    rng_proof: &mut T,
) -> Vec<Option<Vec<ProofDistanceiju>>> {
    let l = n - m + 1;
    let mut proofs: Vec<Option<Vec<ProofDistanceiju>>> = Vec::with_capacity(l * l);

    for i in 0..l {
        for j in 0..l {
            if i.abs_diff(j) <= m/2 || j<i{
                proofs.push(None);
                continue;
            }
            let p_ij = proof_distance_bin_ij(set, &c_vec[i*l+j], &c_bis_vec[i*l+j], &w[i*l+j], u, rng_proof);
            
            proofs.push(Some(p_ij));
        }
    }
    proofs
}

pub fn verify_distance(
    c_vec: &[&[RistrettoPoint]],
    c_bis_vec: &[&[RistrettoPoint]],
    n: usize,
    m: usize,
    set: &Set,
    proofs: &[Option<&[ProofDistanceiju]>],
) -> bool {
    let l = n - m + 1;
    let mut res = true;
    for i in 0..l {
        for j in 0..l {
            if i.abs_diff(j) <= m/2 { continue; }
            let idx = i * l + j;
            match proofs[idx] {
                Some(pij_proofs) => {
                    let ok = verify_distance_bin_ij(c_vec[i*l+j], c_bis_vec[i*l+j], set, pij_proofs);
                    res &= ok;
                }
                _ => {}
            }
        }
    }
    res
}

pub fn measure_time_proof_distance(
    upper: usize,
    n: usize,
    m: usize,
    u: usize,
    iter: usize,
) -> (){
    let mut time_setup              = Duration::ZERO;
    let mut time_commit             = Duration::ZERO;
    let mut time_proof_distance     = Duration::ZERO;
    let mut time_verify_distance    = Duration::ZERO;

    for _ in 0..iter {
        // RNGs
        let mut rng = OsRng;
        let mut rng_k = OsRng;
        let mut rng_proof = OsRng;

        // --- Setup ---
        let t0 = Instant::now();
        let mut set = setup(n, &mut rng);
        time_setup += t0.elapsed();

        // --- Random TS ---
        let ts = random_ecg(&mut rng, n, upper);

        // --- Commit ---
        let c = commit(&mut set, &ts, &mut rng_k);
        
        let g = set.gen;
        let h = set.h_;

        let (_, _, x_diff, k_diff, k_tilde) = calculate_inner_diff_commit(&c, &set, &mut rng_proof);
        
        let t1 = Instant::now();
        let (c_vec, c_bis_vec, w, _) = calculate_dist_commit(&mut rng_proof, n, m, u, g, h, &x_diff, &k_diff, &k_tilde);
        
        let c_vec_refs: Vec<&[RistrettoPoint]> = c_vec.iter().map(|inner| inner.as_slice()).collect();
        let c_bis_vec_refs: Vec<&[RistrettoPoint]> = c_bis_vec.iter().map(|inner| inner.as_slice()).collect();
        let w_refs : Vec<&[Scalar]> = w.iter().map(|inner| inner.as_slice()).collect();

        time_commit += t1.elapsed();

        // --- Proof (distance) ---
        let t2 = Instant::now();
        let proofs_owned = proof_distance(n, m, u, &set, &c_vec_refs, &c_bis_vec_refs, &w_refs, &mut rng_proof);
        time_proof_distance += t2.elapsed();

        // Convert owned Vec<Option<Vec<_>>> -> borrowed Vec<Option<&[_]>>
        let proofs_borrowed: Vec<Option<&[ProofDistanceiju]>> = proofs_owned.iter().map(|opt| opt.as_deref()).collect();

        // --- Verify (distance) ---
        let t3 = Instant::now();
        let ok = verify_distance(&c_vec_refs, &c_bis_vec_refs, n, m, &set, &proofs_borrowed);
        time_verify_distance += t3.elapsed();

        // sanity check
        println!("{}", ok);
        debug_assert!(ok, "distance proof failed verification");
    }

    let it = iter as u32;
    let avg_setup   = time_setup / it;
    let avg_commit  = time_commit / it;
    let avg_proof   = time_proof_distance / it;
    let avg_verify  = time_verify_distance / it;

    println!("Average with n = {}, m = {}, u = {}", n, m, u);
    println!("Setup:   {:?}", avg_setup);
    println!("Commit:  {:?}", avg_commit);
    println!("Proof:   {:?}", avg_proof);
    println!("Verify:  {:?}", avg_verify);
}


//  M_iu = g ^ MPD_iu * h ^ z_iu
pub fn calculate_mpd_commit<T: CryptoRng + RngCore>(
    g: &RistrettoPoint,
    h: &RistrettoPoint,
    mpd: Vec<Vec<Scalar>>, // (MPDi) encoded in binary
    u: usize,
    rng_proof: &mut T,
) -> (Vec<Vec<RistrettoPoint>>, Vec<Vec<RistrettoPoint>>, Vec<Vec<Scalar>>) {

    let l = mpd.len();

    let mut z_vec: Vec<Vec<Scalar>> = Vec::with_capacity(l); // secret keys of (MPDi)
    let mut m_vec: Vec<Vec<RistrettoPoint>> = Vec::with_capacity(l); // commitments of (MPDi) -> (M_iu)
    let mut m_bis_vec: Vec<Vec<RistrettoPoint>> = Vec::with_capacity(l); // commitments of (MPDi) -> (M_iu/g)

    for i in 0..l {
        let mpd_i = &mpd[i];

        // Random z-values
        let zi_pub: Vec<Scalar> = (0..u).map(|_| random_scalar(rng_proof)).collect();
        z_vec.push(zi_pub.clone());

        // Commitments
        let mut mpd_i_commit: Vec<RistrettoPoint> = Vec::with_capacity(u);
        let mut mpd_i_commit_bis: Vec<RistrettoPoint> = Vec::with_capacity(u);

        for bit in 0..u {
            let m_iu = *g * mpd_i[bit] + *h * zi_pub[bit];
            mpd_i_commit.push(m_iu);

            // m' = m - g
            let m_iu_bis = m_iu - *g;
            mpd_i_commit_bis.push(m_iu_bis);
        }

        m_vec.push(mpd_i_commit);
        m_bis_vec.push(mpd_i_commit_bis);
    }

    (m_vec, m_bis_vec, z_vec)
}


// ------------------- Proof MPD bin ---------------------------
// Zero knowledge proof to prove that the MPD have been correctely commited in binary without revealing the values
// OR proof: secret: z_iu 
//  M_iu = h^z_iu or M_iu/g = h^z_iu

pub fn proof_mpd_bin_iu<T: CryptoRng + RngCore>(
    h: &RistrettoPoint,
    m_iu: RistrettoPoint,
    m_iu_bis: RistrettoPoint,      
    ziu: Scalar,     
    rng_proof: &mut T,
) -> ProofMPDBiniu {
    
    let r1: RistrettoPoint;
    let r2: RistrettoPoint;
    let c1: Scalar;
    let c2: Scalar;
    let z1: Scalar;
    let z2: Scalar;

    // Choose which half to simulate based on whether the bit is 0 or 1
    if m_iu == *h * ziu {
        // mpd_iu == 0 branch (simulate the other half)
        let r = random_scalar(rng_proof);
        r1 = h * r;

        z2 = random_scalar(rng_proof);
        c2 = random_scalar(rng_proof);
        r2 = h * z2 - c2 * m_iu_bis;

        let c_chal = chal_distance(&r1, &r2, &h, &m_iu, &m_iu_bis);
        c1 = c_chal - c2;
        z1 = r + c1 * ziu;
    } else {
        let r_ = random_scalar(rng_proof);
        r2 = h * r_;

        z1 = random_scalar(rng_proof);
        c1 = random_scalar(rng_proof);
        r1 = h * z1 - c1 * m_iu;

        let c_chal = chal_distance(&r1, &r2, &h, &m_iu, &m_iu_bis);
        c2 = c_chal - c1;
        z2 = r_ + c2 * ziu;
    }

    ProofMPDBiniu { r_1: r1, r_2: r2, c_1: c1, c_2: c2, response_1: z1, response_2: z2 }
}

pub fn proof_mpd_bin_i<T: CryptoRng + RngCore>(
    h: &RistrettoPoint,
    m_i: &[RistrettoPoint],      
    m_i_bis: &[RistrettoPoint],
    z_i: &[Scalar],
    u: usize,
    rng_proof: &mut T,
) -> Vec<ProofMPDBiniu> {             
    let mut proof_mpd_i:  Vec<ProofMPDBiniu>   = Vec::with_capacity(u);
    for bit in 0..u {
        let proof = proof_mpd_bin_iu(h, m_i[bit], m_i_bis[bit], z_i[bit], rng_proof);
        proof_mpd_i.push(proof);
    }
    proof_mpd_i
}


pub fn verify_MPD_bin_i(
    m_i: &[RistrettoPoint],  
    set: &Set,
    proofs: &[ProofMPDBiniu],
) -> bool {
    let u = proofs.len();
    if m_i.len() != u { return false; }

    let g = set.gen;
    let h = set.h_;

    for idx in 0..u {
        let res_1 = proofs[idx].response_1;
        let res_2 = proofs[idx].response_2;
        let r1    = proofs[idx].r_1;
        let r2    = proofs[idx].r_2;
        let c1    = proofs[idx].c_1;
        let c2    = proofs[idx].c_2;

        let c_u      = m_i[idx];
        let c_u_bis  = c_u - g;

        let c = chal_distance(&r1, &r2, &h, &c_u, &c_u_bis);

        // res_1*h == r1 + c1*c_u  AND  res_2*h == r2 + c2*c_u_bis  AND  c == c1 + c2
        if (h * res_1 != r1 + c1 * c_u) || (h * res_2 != r2 + c2 * c_u_bis) || (c != c1 + c2) {
            return false;
        }
    }
    true
}

pub fn proof_MPD_bin<T: CryptoRng + RngCore>(
    m_vec: &[Vec<RistrettoPoint>],           
    m_bis_vec: &[Vec<RistrettoPoint>],    
    z_vec: &[Vec<Scalar>],
    n: usize,
    m: usize,
    u: usize,
    h: &RistrettoPoint,
    rng_proof: &mut T,
) -> Vec<Vec<ProofMPDBiniu>> {
    let w = n - m + 1;

    let mut proofs: Vec<Vec<ProofMPDBiniu>> = Vec::with_capacity(w);

    for i in 0..w {
        let p_i = proof_mpd_bin_i(h, &m_vec[i], &m_bis_vec[i], &z_vec[i], u, rng_proof);
        proofs.push(p_i);
    }
    proofs
}

pub fn verify_MPD_bin(
    n: usize,
    m: usize,
    commits_opt: &Vec<Vec<RistrettoPoint>>,
    set: &Set,
    proofs_opt: &Vec<Vec<ProofMPDBiniu>>,
) -> bool {
    let w = n - m + 1;
    debug_assert_eq!(commits_opt.len(), w);
    debug_assert_eq!(proofs_opt.len(),  w);

    let mut res = true;
    for i in 0..w {
        let commits_i = &commits_opt[i];
        let proofs_i = &proofs_opt[i];
        res &= verify_MPD_bin_i(&commits_i, set, &proofs_i);
        if res==false{
            println!("Error at i = {}", i);
        }
    }
    res
}

pub fn measure_time_proof_MPD(
    upper: usize,
    n: usize,
    m: usize,
    u: usize,
    iter: usize,
) {
    let mut time_setup           = Duration::ZERO;
    let mut time_commit          = Duration::ZERO;
    let mut time_proof_mpd       = Duration::ZERO;
    let mut time_verify_mpd      = Duration::ZERO;

    for _ in 0..iter {
        let mut rng = OsRng;
        let mut rng_k = OsRng;
        let mut rng_proof = OsRng;

        let ts = random_ecg(&mut rng, n, upper);

        // Compute MPD and bit-decompose (u bits per index)
        let mpd      = compute_mpd_with_window_scalar(&ts, m);
        let mpd_bin: Vec<Vec<Scalar>> = mpd.iter().map(|x| scalar_to_bits(x, u)).collect();

        // Setup
        let t0 = Instant::now();
        let mut set = setup(n, &mut rng);
        time_setup += t0.elapsed();

        // Commit (not used by these MPD proofs but kept for parity)
        let t1 = Instant::now();
        let c = commit(&mut set, &ts.to_vec(), &mut rng_k);
        let g = set.gen;
        let h = set.h_;
        let (m_vec, m_bis_vec, z_vec) = calculate_mpd_commit(&g, &h, mpd_bin, u, &mut rng_proof);
        time_commit += t1.elapsed();

        // Prove MPD bits
        let t2 = Instant::now();
        let proofs_owned = proof_MPD_bin(&m_vec, &m_bis_vec, &z_vec, n, m, u, &h, &mut rng_proof);
        time_proof_mpd += t2.elapsed();

        // Verify
        let t3 = Instant::now();
        let ok = verify_MPD_bin(n, m, &m_vec, &set, &proofs_owned);
        time_verify_mpd += t3.elapsed();

        println!("{}", ok);
        debug_assert!(ok, "MPD bit proof failed verification");
    }

    let it = iter as u32;
    println!("Average with n = {}, m = {}, u = {}", n, m, u);
    println!("Setup:   {:?}", time_setup  / it);
    println!("Commit:  {:?}", time_commit / it);
    println!("Proof:   {:?}", time_proof_mpd / it);
    println!("Verify:  {:?}", time_verify_mpd / it);
}

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
            res &= (h * z_i == r_i + y_u*c_i);
        }
    }
    // verify c
    let c = chal_list(&proofs_exist.r_i, &y_i, &g_i);
    let mut c_to_test : Scalar = Scalar::ZERO;
    for c_i in proofs_exist.c_i.clone(){
        c_to_test += c_i;
    }
    res &= (c_to_test == c);
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
        
        let (d_vec, _, w, _) = calculate_dist_commit(&mut rng_proof, n, m, u, g, h, &x_diff, &k_diff, &k_tilde);

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

// -------------- MPD min -------
// pub fn list_relation(
//     mut cmpt: usize,
//     mpd_bin: Vec<Scalar>,
//     d_ij: &[Scalar],
//     mut found: bool,
//     mut list: Vec<bool>
// ) -> Vec<bool>{
// 	while (found == false) && (cmpt > 0){
// 		if d_ij[cmpt-1] - mpd_bin[cmpt-1] == Scalar::ONE {
// 			list[2*cmpt-1] = true; // corresponds to y_{2l}
// 			found = true;
// 		}
// 		else{
// 			list[2*cmpt-2] = true; // corresponds to y_{2l-1}	
// 			cmpt = cmpt - 1;
// 			list_relation(cmpt,mpd_bin.clone(),d_ij.clone(),found,list.clone());
// 		}
// 	}
//     // println!("cmpt = {}", cmpt);
// 	return list;
// }
pub fn list_relation(
    mpd_bin: Vec<Scalar>,
    d_ij: &[Scalar],
    ell: usize
) -> Vec<bool>{
    let mut cmpt = ell;
    let mut list: Vec<bool> = vec![false; 2*ell];
	while cmpt > 0{
		if d_ij[cmpt-1] - mpd_bin[cmpt-1] == Scalar::ONE {
			list[2*cmpt-1] = true; // corresponds to y_{2l-1}
            break;
		}
		else{
			list[2*cmpt-2] = true; // corresponds to y_{2l}	
			cmpt = cmpt - 1;
		}
	}
    // println!("cmpt = {}", cmpt);
	return list;
}


// function for a given i
pub fn prove_min<T: CryptoRng + RngCore>(rng: &mut T, y: &[RistrettoPoint],h: RistrettoPoint,mut alpha: &[Scalar],mut list: Vec<bool>) -> ZKmin{
	let l = y.len() / 2;
	let mut r: Vec<Scalar> = vec![Scalar::from(0u64);2*l]; // vector of random 
	let mut rr: Vec<RistrettoPoint> = vec![RistrettoPoint::identity();2*l]; // vector of commitments
	let mut c: Vec<Scalar> = vec![Scalar::from(0u64);2*l]; // vector of challenges
	let mut u: Vec<Scalar> = vec![Scalar::from(0u64);2*l]; // vector of responses
	
	let mut first = 0;
	while list[first] == false{
		first +=1;
	}
    // println!("{:?}", list);
	
	// Commitment Phase
	for i in 0..2*l{
		if list[i] == true{
			r[i] = random_scalar(rng);
			rr[i] = r[i] * h;
		}
		else{
			u[i] = random_scalar(rng); 	// responses for the simulated relations
		}
	}
	
	if first > 1{  // simulates for the relations 1 and 2
		c[0] = random_scalar(rng);
		rr[0] = u[0] * h - c[0] * y[0];
		c[1] = random_scalar(rng);
		rr[1] = u[1] * h - c[1] * y[1];
	}
	
	else{ // simulates for the relation 1 or 2
		if list[0] == true{ // simulates the challenge for the relation 2
			c[1] = random_scalar(rng);
			rr[1] = u[1] * h - c[1] * y[1];	
		}
		else{ // simulates the challenge for the relation 1
			c[0] = random_scalar(rng);
			rr[0] = u[0] * h - c[0] * y[0];
		}
	}
	
	// Simulates the relations between 3 and first-1 and consider the equation c[2k] = c[2k-1] xor c[2k-2] (k in [1;l-1]) and chal_gen = c[2l-1] xor c[2l-2]
	for i in 2..first{
		if i % 2 == 0{ // the challenge of the right relation is computed from the two previous challenges
			c[i] = c[i-1] + c[i-2];
			rr[i] = u[i] * h - c[i] * y[i];
		}
		else{ // the challenge of the left part is randomly picked
			c[i] = random_scalar(rng);
			rr[i] = u[i] * h - c[i] * y[i];
		}
	}
	
	for i in first+1..2*l{ //simulates for the relations i between first + 1 (because list[first] = 1) and 2*l-1 s.t. list[i] = 0 
		if list[i] == false{
			c[i] = random_scalar(rng);
			rr[i] = u[i] * h - c[i] * y[i];
		}
	}
	
	// Challenge Phase
	let chal_gen = chal_list(&rr.clone(),&y.clone(),&vec![h;2*l]);
	
	// Challenges + responses for the verified relations
	if list[2*l-2] == true{ // list = 0...010
		c[2*l-2] = chal_gen - c[2*l-1];
		u[2*l-2] = r[2*l-2] + c[2*l-2] * alpha[2*l-2];
	}
	if list[2*l-1] == true{ // list = 0...01
		c[2*l-1] = chal_gen - c[2*l-2];
		u[2*l-1] = r[2*l-1] + c[2*l-1] * alpha[2*l-1];
	}
	
	for i in (first..2*l-2).rev(){ // i in [first, 2l-3]
		if list[i] == true && i % 2 == 0  && i > 1{
			c[i] = c[i+2] - c[i+1];
			u[i] = r[i] + c[i] * alpha[i];
		}
		if list[i] == true && i % 2 == 1 && i > 1{
			c[i] = c[i+1] - c[i-1];
			u[i] = r[i] + c[i] * alpha[i];
		}
	}
	
	if list[1] == true{
		c[1] = c[2] - c[0];
		u[1] = r[1] + c[1] * alpha[1];
	}
		
	if list[0] == true{
	    c[0] = c[2] - c[1];
	   	u[0] = r[0] + c[0] * alpha[0];
	}
	
	// alpha.zeroize();
	// r.zeroize();
	// list.zeroize();
	
	return ZKmin{ commitments: rr, challenges: c, responses: u }
}

pub fn verify_min(proof: &ZKmin, y: Vec<RistrettoPoint>,h: RistrettoPoint) -> bool{
	
	// Parses the proof
	let rr = &proof.commitments;
	let c = &proof.challenges;
	let u = &proof.responses;
	
	let l = y.len() / 2;
	
	// Recomputes the general challenge
	let chal_gen = chal_list(&rr.clone(),&y.clone(),&vec![h;y.len()]);
	
	if chal_gen != c[2*l-1] + c[2*l-2]{
        println!("Challenge error");
		return false
	}
    for i in 2..l{
		if c[2*i-2] != c[2*i-3] + c[2*i-4]{
			println!("{:?}, {}",c[2*i-2] == c[2*i-3] + c[2*i-4],i);
			return false
		}
	}
	for i in 0..2*l-1{
		if rr[i] != u[i] * h - c[i] * y[i]{
            println!("Error at indice {}", i);
			return false	
		}
	}
	
	return true
}


pub fn proof_mpd_min<T: CryptoRngCore>(
    mpd_bin: Vec<Vec<Scalar>>, // [MPD_i_binary]
    d_ij: &[&[Scalar]], // [d_i_j_binary]
    h: &RistrettoPoint,
    l: usize, // l = n-m+1, length of MPD
    _k: usize,
    m: usize,
    alpha_list: &[&[Scalar]], // list of secrets
    y_list: &[&[RistrettoPoint]], // list of commitments
    proof_rng: &mut T,
    is_real_relation: &[bool]
)->Vec<Option<ZKmin>>{
    let mut proof_list : Vec<Option<ZKmin>> = Vec::with_capacity(l*l);
    for i in 0..l{
        // println!("i = {}", i);
        for j in 0..l{
            // println!("j = {}", j);
            if i.abs_diff(j) <= m/2{
                proof_list.push(None);
                continue;
            }
            else{
                let alpha = &alpha_list[i*l+j];
                let y = &y_list [i*l+j];
                let rels = y.len();
                
                assert!(rels % 2 == 0, "y.len() must be even, got {}", rels); // should be equals to 2*u
                let k_local = rels / 2;

                // let mut list = vec![false;rels];
                // let cmpt = k_local;
                // let found = false;

                // let t_list = Instant::now();
    	        // let list = list_relation(cmpt, mpd_bin[i].clone(), d_ij[i*l+j].clone(), found, list);
                let list = list_relation(mpd_bin[i].clone(), d_ij[i*l+j].clone(), k_local);
                // println!("Time list relation: {:?}",t_list.elapsed());
                // println!("{:?}", list);
                // let t_prove = Instant::now();
                let proof = prove_min(proof_rng, y.clone(), h.clone(), alpha.clone().clone(), list.clone());
                // println!("Time prove min: {:?}",t_prove.elapsed());
                proof_list.push(Some(proof));
            }
        }
    }
    proof_list
}

pub fn verify_mpd_min<T: CryptoRngCore>(
    h: &RistrettoPoint,
    l: usize, 
    m: usize,
    y_list: &[Vec<RistrettoPoint>],
    proof_rng: &mut T,
    proof_list: &[Option<ZKmin>]
)->bool{
    let mut res : bool = true;
    for i in 0..l{
        for j in 0..l{
            if i.abs_diff(j) <= m/2{
                continue;
            }
            else{
                let y = &y_list [i*l+j];
                let proof_ref: &ZKmin = match &proof_list[i*l+j] {
                    Some(p) => p,       
                    None => {
                        return false;
                    }
                };
                res &= verify_min(proof_ref, y.clone(), h.clone());
            }
        }
    }
    res
}

pub fn measure_time_mpd_min(
    upper: usize,
    n: usize,   // length of time series
    m: usize,   // window size
    ell: usize, // number of bits (ℓ)
    iter: usize,
) {
    // let a = n - m + 1; // number of MPD entries (indices i ∈ I

    let mut time_setup      = Duration::ZERO;
    let mut time_commit     = Duration::ZERO;
    let mut time_proof_mpd  = Duration::ZERO;
    let mut time_verify_mpd = Duration::ZERO;

    for _ in 0..iter {
        let mut rng       = OsRng;
        let mut rng_k     = OsRng;
        let mut rng_proof = OsRng;
        // let mut rng_dist  = OsRng;

        let t0 = Instant::now();
        let mut set = setup(n, &mut rng);
        time_setup += t0.elapsed();

        // --- 1) Compute MPD(i) for each i -------------------------------
        let ts = random_ecg(&mut rng, n, upper);
        // println!("{:?}", ts);

        let t1 = Instant::now();
        let commitment = commit(&mut set, &ts.to_vec(), &mut rng_k);

        // let x = &commitment.x_;
        // let k = &commitment.k_;
        let n = set.n_;
        let g = set.gen;
        let h = set.h_;

        // calculate commit
        let (_, _, x_diff, k_diff, k_tilde) = calculate_inner_diff_commit(&commitment, &set, &mut rng_proof);
        
        let (d_vec, _, w, d_private_vec) = calculate_dist_commit(&mut rng_proof, n, m, ell, g, h, &x_diff, &k_diff, &k_tilde);
        
        // MPD
        let mpd      = compute_mpd_with_window_scalar(&ts, m);
        let mpd_bin: Vec<Vec<Scalar>> = mpd.iter().map(|x| scalar_to_bits(x, ell)).collect();

        let (m_vec, _, z_vec) = calculate_mpd_commit(&g, &h, mpd_bin.clone(), ell, &mut rng_proof);

        let m_vec_refs: Vec<&[RistrettoPoint]> = m_vec.iter().map(|inner| inner.as_slice()).collect();
        let z_vec_refs: Vec<&[Scalar]> = z_vec.iter().map(|inner| inner.as_slice()).collect();
        let d_vec_refs: Vec<&[RistrettoPoint]> = d_vec.iter().map(|inner| inner.as_slice()).collect();
        let w_refs : Vec<&[Scalar]> = w.iter().map(|inner| inner.as_slice()).collect();
        let d_private_refs : Vec<&[Scalar]> = d_private_vec.iter().map(|inner| inner.as_slice()).collect();

        // println!("MPD: {:?}", mpd);
        let a = mpd.len();
        
        let mut alpha_list : Vec<Vec<Scalar>> = Vec::with_capacity(a*a);
        let mut y_list : Vec<Vec<RistrettoPoint>> = Vec::with_capacity(a*a);

        for i in 0..a{
            for j in 0..a{
                let mut alpha_buffer : Vec<Scalar> = Vec::with_capacity(2*ell);
                let mut y_buffer : Vec<RistrettoPoint> = Vec::with_capacity(2*ell);
                for bit in 0..ell{
                    let alpha_i_ell_ = z_vec_refs[i][bit] - w_refs[i*a+j][bit];
                    alpha_buffer.push(alpha_i_ell_);
                    alpha_buffer.push(alpha_i_ell_);
                    let y_buffer_pair_ = m_vec_refs[i][bit] - d_vec_refs[i*a+j][bit];
                    let y_buffer_impair_ = m_vec_refs[i][bit] - d_vec_refs[i*a+j][bit] + g;
                    y_buffer.push(y_buffer_pair_);
                    y_buffer.push(y_buffer_impair_);
                }
                alpha_list.push(alpha_buffer.clone());
                y_list.push(y_buffer.clone());
            }
        }

        let y_list_refs: Vec<&[RistrettoPoint]> = y_list.iter().map(|inner| inner.as_slice()).collect();
        let alpha_list_refs : Vec<&[Scalar]> = alpha_list.iter().map(|inner| inner.as_slice()).collect();


        let tak = t1.elapsed();
        time_commit += tak;
        println!("Commit time {:?}", tak);

        // initiate is_real_relation list
        let is_real_relation = vec![false; 2 * ell];

        // --- 6) PROOF time ----------------------------------------------
        let t_proof = Instant::now();
        let proof_list = proof_mpd_min(
            mpd_bin.clone(),
            &d_private_refs,
            &h,
            a,              // l = number of indices
            ell,            // k = number of bits per index (or your tree depth parameter)
            m,            
            &alpha_list_refs,
            &y_list_refs,
            &mut rng_proof,
            &is_real_relation,
        );
        time_proof_mpd += t_proof.elapsed();

        println!("  proof (MIN):   {:?}", time_proof_mpd);

        // --- 7) VERIFY time ---------------------------------------------
        let t_verify = Instant::now();
        let ok = verify_mpd_min(
            &h,
            a,              // l
            m,            // m (as in your verify_mpd_min signature)
            &y_list,
            &mut rng_proof,
            &proof_list,
        );
        time_verify_mpd += t_verify.elapsed();
        println!("  verify (MIN):  {:?}", time_verify_mpd);

        println!("{:?}",ok);
        debug_assert!(ok, "verify_mpd_min failed!");
    }

    println!("==== MPD-MIN timing over {} iterations ====", iter);
    println!("  setup:         {:?}", time_setup/(iter as u32));
    println!("  commit:        {:?}", time_commit/(iter as u32));
    println!("  proof (MIN):   {:?}", time_proof_mpd/(iter as u32));
    println!("  verify (MIN):  {:?}", time_verify_mpd/(iter as u32));
}

// ----------- Threshold i -------------
pub fn prove_threshold_i<T: CryptoRng + RngCore>(
    rng: &mut T,
    y: &[RistrettoPoint],
    h: RistrettoPoint,
    alpha: &[Scalar],
    epsilon_bin: &[usize]
)->ZKthresholdi{
    let offset = epsilon_bin[0];
    let l = y.len() - offset;
    // println!("l = {}", l);
    let y_view = &y[offset..];  
    let alpha_view = &alpha[offset..];

    let mut r: Vec<Scalar> = vec![Scalar::from(0u64);l]; // vector of random 
	let mut rr: Vec<RistrettoPoint> = vec![RistrettoPoint::identity();l]; // vector of commitments
	let mut c: Vec<Scalar> = vec![Scalar::from(0u64);l]; // vector of challenges
	let mut u: Vec<Scalar> = vec![Scalar::from(0u64);l]; // vector of responses

    // deduce the first y that is true if the right relation is simulated
    let mut first: usize = 0;
    let mut list_relation : Vec<bool> = vec![false;l];
    for ind in epsilon_bin{
        list_relation[ind-offset] = true;
    }
    let last = epsilon_bin.len()-1;
    let mut found = false;
    for ind in epsilon_bin[last]-offset+1..l{
        // println!("{}", ind);
        if y_view[ind] == alpha_view[ind] * h{
            // println!("enter in the first or");
            list_relation[ind] = true;
            found = true;
            for _j in 0..ind{
                list_relation[_j] = false;
            }
            break;
        }
    }
    if found==false{
        for ind_u in (0..last).rev(){
            let min = epsilon_bin[ind_u]-offset;
            let max = epsilon_bin[ind_u+1]-offset;
            for t in min+1..max{
                if y_view[t] == alpha_view[t] * h{
                    list_relation[t] = true;
                    for _ in 0..t{
                        list_relation[t] = false;
                    }
                    break;
                }
            }
        }
    }

    // deduce the first true relation from right
    while list_relation[first]==false{
        first+=1;
    }
    // generate vlidation list for epsilon_bin
    let mut list_epsilon_bool : Vec<bool> = vec![false; l];
    for bit in epsilon_bin{
        list_epsilon_bool[bit-offset] = true;
    }


    // commitment phase
    for i in 0..l{
        if list_relation[i]{
            r[i] = random_scalar(rng);
            rr[i] = r[i] * h;
        }else{
            u[i] = random_scalar(rng);
        }
    }

    if epsilon_bin.len()<2{
        println!("epsilon bit length < 2");
        let mut c_sum = Scalar::ZERO;
        for i in 0..l{
            if list_relation[i]==false{
                c[i] = random_scalar(rng);
                c_sum += c[i];
                rr[i] = u[i] * h - c[i] * y_view[i];
            }
        }
        let chal_gen = chal_list(&rr.clone(),&y_view.clone(),&vec![h;l]);
        c[first] = chal_gen - c_sum;
        u[first] = r[first] + c[first] * alpha_view[first];

        return ZKthresholdi{commitments: rr, challenges: c, responses: u};
    }
    if first > epsilon_bin[1]-offset{
        let mut ind_c : usize;
        for ind_bit in epsilon_bin[0]..epsilon_bin[1]{
            ind_c = ind_bit - offset;
            c[ind_c] = random_scalar(rng);
            rr[ind_c] = u[ind_c] * h - c[ind_c] * y_view[ind_c];
        }
    }
    else{
        for i in epsilon_bin[0]-offset..first{
            c[i] = random_scalar(rng);
            rr[i] = u[i] * h - c[i] * y_view[i];
        }
        for i in first+1..epsilon_bin[1]-offset{
            c[i] = random_scalar(rng);
            rr[i] = u[i] * h - c[i] * y_view[i];
        }
    }

    // compute the challenges for the simulated relations
    let mut cursor = 0;
    for i in epsilon_bin[1]-offset..first{
        if list_epsilon_bool[i]{
            let u_ind = epsilon_bin[cursor]-offset;
            let mut c_sum = Scalar::ZERO;
            for j in u_ind..i{
                c_sum += c[j];
            }
            c[i] = c_sum;
            rr[i] = u[i] * h - c[i] * y_view[i];
            cursor+=1;
        }else{
            c[i] = random_scalar(rng);
            rr[i] = u[i]*h - c[i] * y_view[i];
        }
    }
    for i in first+1..l{
        if list_relation[i] == false{
            c[i] = random_scalar(rng);
            rr[i] = u[i] * h - c[i] * y_view[i];
        }
    }

    for i in 0..l {
        if !list_relation[i] && c[i] == Scalar::from(0u64) {
            // This simulated index wasn't assigned anywhere above
            c[i] = random_scalar(rng);
            rr[i] = u[i] * h - c[i] * y_view[i];
        }
    }


    // challenge + response phase
    let chal_gen = chal_list(&rr.clone(),&y_view.clone(),&vec![h;l]);

    // left tail
    let alpha_bit = epsilon_bin[epsilon_bin.len()-1]-offset;
    if list_relation[alpha_bit] {
        // Case: real relation exactly at u_alpha
        let mut buffer = Scalar::ZERO;
        for j in alpha_bit + 1 .. l {
            buffer += c[j];
        }
        c[alpha_bit] = chal_gen - buffer;
        u[alpha_bit] = r[alpha_bit] + c[alpha_bit] * alpha_view[alpha_bit];
    } else {
        // Case: the real relation is somewhere in (alpha_bit+1 .. l-1] 
        let mut c_sum = chal_gen - c[alpha_bit];
        let mut true_bit = alpha_bit + 1; 
    
        for i in alpha_bit + 1 .. l {
            if !list_relation[i] {
                c_sum -= c[i];
            } else {
                true_bit = i;
            }
        }
    
        c[true_bit] = c_sum;
        u[true_bit] = r[true_bit] + c[true_bit] * alpha_view[true_bit];
    }

    // right tail
    let mut alpha_1_bit = epsilon_bin[epsilon_bin.len()-2]-offset;
    let mut cursor = alpha_bit;
    for i in first+1..alpha_1_bit{
        if list_relation[i] && list_epsilon_bool[i] && i>1{
            let mut c_sum = Scalar::ZERO;
            for j in i+1..cursor+1{
                c_sum += c[j];
            }
            c[i] = c_sum;
            u[i] = r[i] + c[i] * alpha_view[i];
        }
    }
    alpha_1_bit = epsilon_bin[1]-offset;
    let mut c_sum = Scalar::ZERO;
    let mut maybe_true_ind: Option<usize> = None;

    for ind in 0..alpha_1_bit {
        if list_relation[ind] {
            maybe_true_ind = Some(ind);
        } else {
            c_sum += c[ind];
        }
    }

    if let Some(true_ind) = maybe_true_ind {
        c[true_ind] = c[alpha_1_bit] - c_sum;
        u[true_ind] = r[true_ind] + c[true_ind] * alpha_view[true_ind];
    } else {
        // No real index in this block => all are simulated.
        // Do NOT touch u[...] here; keep them simulated.
        // If you still need the block constraint c[alpha_1_bit] = sum(left..right-1),
        // you must have enforced it earlier using only simulated c's.
    }


    return ZKthresholdi{commitments: rr, challenges: c, responses: u};
}

pub fn prove_threshold<T: CryptoRng + RngCore>(
    rng: &mut T,
    y_list: &[Vec<RistrettoPoint>],
    h: RistrettoPoint,
    alpha_list: &[Vec<Scalar>],
    epsilon_bin: &[usize]
)->Vec<ZKthresholdi>{
    let mut proofs : Vec<ZKthresholdi> = Vec::with_capacity(y_list.len());
    for i in 0..y_list.len(){
        let y = &y_list[i];
        let alpha = &alpha_list[i];
        let proof = prove_threshold_i(rng, &y, h, &alpha, epsilon_bin);
        proofs.push(proof);
    }
    proofs
}

pub fn verify_threshold_i(
    proof: &ZKthresholdi, 
    y: Vec<RistrettoPoint>,
    h: RistrettoPoint,
    epsilon_bin: &[usize]) -> bool{
	
	// Parses the proof
	let rr = &proof.commitments;
	let c = &proof.challenges;
	let u = &proof.responses;

    let offset = epsilon_bin[0];

    let alpha = epsilon_bin[epsilon_bin.len()-1]-offset;
	
	let l = y.len()-offset;
	
	// Recomputes the general challenge
    let y_view = &y[offset..];  
	let chal_gen = chal_list(&rr.clone(),&y_view.clone(),&vec![h;l]);
	
    let mut buffer = Scalar::ZERO;
    
    for i in alpha..l{
        buffer += c[i];
    }
	if chal_gen != buffer{
        println!("challenge failed");
		return false
	}

	for i in 0..l{
		if rr[i] != u[i] * h - c[i] * y_view[i]{
            println!("response verification failed for {}", i);
			return false	
		}
	}
	
	for b in 0..epsilon_bin.len() - 1 {
        let left = epsilon_bin[b] - offset;
        let right = epsilon_bin[b+1] - offset;
    
        let mut c_sum = Scalar::ZERO;
        for j in left..right {
            c_sum += c[j];
        }
    
        if c[right] != c_sum {
            println!("False , block {}", b);
            return false;
        }
    }
	return true
}

pub fn verify_threshold(
    h: &RistrettoPoint,
    y_list: &[Vec<RistrettoPoint>],
    proof_list: &[ZKthresholdi],
    epsilon_bin: &[usize]
)->bool{
    let mut res : bool = true;
    let l = y_list.len();
    for i in 0..l{
        let y = &y_list[i];
        let proof_ref = &proof_list[i];
        res &= verify_threshold_i(proof_ref, y.clone(), h.clone(), epsilon_bin.clone());
        
    }
    res
}

pub fn measure_time_non_similarity(
    upper: usize,
    n: usize,   // length of time series
    m: usize,   // window size
    ell: usize, // number of bits (ℓ)
    iter: usize,
    epsilon: u64
) {
    let a = n - m + 1; // number of MPD entries (indices i ∈ I

    let mut time_setup      = Duration::ZERO;
    let mut time_commit     = Duration::ZERO;
    let mut time_proof_threshold  = Duration::ZERO;
    let mut time_verify_threshold = Duration::ZERO;

    for _ in 0..iter {
        let mut rng       = OsRng;
        let mut rng_k     = OsRng;
        let mut rng_proof = OsRng;
        // let mut rng_dist  = OsRng;

        // --- 1) Compute MPD(i) for each i -------------------------------
        let ts = random_ecg(&mut rng, n, upper);
        let mpd = compute_mpd_with_window_scalar(&ts, m); // length a
        // println!("{:?}", mpd);
        // Binary decomposition MPD_i -> {MPD_{i,u}}_{u=0..ell-1}
        let mpd_bits: Vec<Vec<Scalar>> = mpd
            .iter()
            .map(|val| scalar_to_bits(val, ell)) // each is length ell, bits 0/1 as Scalar
            .collect();

        // --- 2) Setup ----------------------------------------------------
        let t0 = Instant::now();
        let mut set = setup(n, &mut rng);
        time_setup += t0.elapsed();

        let g = set.gen;
        let h = set.h_;
        // let n_set = set.n_;

        // --- 3) Commit original time series (for distances etc.) --------
        let t1 = Instant::now();
        let commitment = commit(&mut set, &ts.to_vec(), &mut rng_k);

        // let x_enc = &commitment.x_;
        // let k_enc = &commitment.k_;

        // --- 4) Build MPD bit commitments M_{i,u} and store z_{i,u} -----
        //
        // M_{i,u} = g^{MPD_{i,u}} h^{z_{i,u}}
        // z_{i,u} random scalar
        //
        let mut Y_list: Vec<Vec<RistrettoPoint>> = Vec::with_capacity(a);
        let mut z_list: Vec<Vec<Scalar>>         = Vec::with_capacity(a); // z_{i,u}


        for i in 0..a {
            let mut Y_i: Vec<RistrettoPoint> = Vec::with_capacity(ell);
            let mut zi: Vec<Scalar>         = Vec::with_capacity(ell);

            for u_idx in 0..ell {
                let bit = mpd_bits[i][u_idx];         // MPD_{i,u} ∈ {0,1}
                let z_iu = random_scalar(&mut rng_proof); // z_{i,u} ∈ Z_p
                let M_iu = g * bit + h * z_iu;        // Pedersen-like commitment

                Y_i.push(M_iu - g);
                zi.push(z_iu);
            }

            Y_list.push(Y_i);
            z_list.push(zi);
        }

        let epsilon_bin_val = scalar_to_bits(&Scalar::from(epsilon), ell);
        let mut epsilon_bin : Vec<usize> = Vec::with_capacity(ell);
        for bit in 0..epsilon_bin_val.len(){
            if epsilon_bin_val[bit] == Scalar::ONE{
                epsilon_bin.push(bit);
            }
        }
        // println!("{:?}", epsilon_bin);

        time_commit += t1.elapsed();

        // println!("  commit:        {:?}", time_commit);

        // --- 6) PROOF time ----------------------------------------------
        let t_proof = Instant::now();
        let proof_list = prove_threshold(
            &mut rng_k,
            &Y_list,
            h,
            &z_list,
            &epsilon_bin
        );
        time_proof_threshold += t_proof.elapsed();

        // println!("  proof (MIN):   {:?}", time_proof_threshold);

        // --- 7) VERIFY time ---------------------------------------------
        let t_verify = Instant::now();
        let ok = verify_threshold(
            &h,
            &Y_list,
            &proof_list,
            &epsilon_bin
        );

        time_verify_threshold += t_verify.elapsed();
        // println!("  verify (THRESHOLD):  {:?}", time_verify_threshold);

        println!("{:?}",ok);
        debug_assert!(ok, "verify_threshold failed!");
    }

    println!("==== THRESHOLD timing over {} iterations ====", iter);
    println!("  setup:         {:?}", time_setup/(iter as u32));
    println!("  commit:        {:?}", time_commit/(iter as u32));
    println!("  proof (Threshold):   {:?}", time_proof_threshold/(iter as u32));
    println!("  verify (Threshold):  {:?}", time_verify_threshold/(iter as u32));
}

// u_alpha and rel_list are offseted
pub fn relation_check(
    rel_list : &[bool],
    l: usize, // bit length
    u_alpha: &[usize]
)->bool{
    let mut res = false;
    let alpha = u_alpha.len()-1;
    let mut cursor = alpha;
    let mut begin : usize;
    let mut end : usize;

    while(cursor>=0 && res==false){
        // begin = 0 if cursor == 1 else u_alpha[cursor-1]+1;
        if cursor == 0 {
            begin = 0;
        }else{
            begin = u_alpha[cursor]+1;
        }
        //end = l if cursor == alpha else u_alpha[cursor]-1;
        if cursor == alpha{
            end = l-1;
        }else{
            end = u_alpha[cursor+1]-1;
        }
        // println!("begin = {}, end = {}", begin, end);
        // verify bigvee
        for bit in begin..end+1{
            // println!("bit: {}", bit);
            if rel_list[bit]{
                res = true;
                break;
            }
        }
        if res==false{
            if cursor==0{
                break;
            }
            if rel_list[begin-1]==false{
                break
            }

        }
        cursor -= 1;
    }
    res
}

pub fn prove_non_anomaly_i<T: CryptoRngCore>(
    u_alpha: &[usize], // zero bits indices
    d_vec: &[&[RistrettoPoint]], // D_iju the commitments of d_iju
    w_vec: &[&[Scalar]], // w_iju the secret key of d_iju
    h: RistrettoPoint,
    rng_proof: &mut T
)->Vec<ZKthresholdi>{
    let a = d_vec.len(); //number of j
    let offset = u_alpha[0];
    let u_alpha_view : Vec<usize> = u_alpha.iter().map(|val| val-offset).collect();
    // println!("u alpha : {:?}", u_alpha_view);
    let l = d_vec[0].len() - offset;
    let mut d_ij : &[RistrettoPoint];
    let mut w_ij : &[Scalar];
    let mut j_star = a; // when no j_star found
    for j in 0..a{
        d_ij = d_vec[j];
        w_ij = w_vec[j];
        let d_ij_view : &[RistrettoPoint] = &d_ij[offset..];
        let w_ij_view : &[Scalar] = &w_ij[offset..];
        let rel_list : Vec<bool> = (0..l).map(|bit| d_ij_view[bit]==w_ij_view[bit]*h).collect();
        if relation_check(&rel_list, l, &u_alpha_view){
            j_star = j;
            break;
        }
    }
    if j_star==a{
        println!("Error! no j star found");
    }

    let mut simulate_proofs : Vec<ZKthresholdi> = Vec::with_capacity(a-1);
    let mut simulate_chal_sum = Scalar::ZERO;
    for j in 0..a{
        if j != j_star{
            let (proof_j, chal_j) = simulate_pi_1(&u_alpha_view, &d_vec[j][offset..], h, rng_proof);
            simulate_proofs.push(proof_j);
            simulate_chal_sum += chal_j;
        }
    }

    // j_star
    let d_ij_star = d_vec[j_star];
    let w_ij_star = w_vec[j_star];
    let d_ij_star_view : &[RistrettoPoint] = &d_ij_star[offset..];
    let w_ij_star_view : &[Scalar] = &w_ij_star[offset..];
    let mut r_j_star : Vec<Scalar> = vec![Scalar::ZERO; l];
    let mut u_j_star : Vec<Scalar> = vec![Scalar::ZERO; l];
    let mut rr_j_star: Vec<RistrettoPoint> = vec![RistrettoPoint::identity(); l];
    let mut c_j_star: Vec<Scalar> = vec![Scalar::ZERO; l];

    // deduce the bool list for j_star
    let mut rel_list_j_star : Vec<bool> = vec![false;l];
    for ind in &u_alpha_view{
        rel_list_j_star[*ind] = true;
    }
    let last = u_alpha_view.len()-1; // 0
    let mut first_true_from_right = 0;
    let mut nearest_alpha_index_right = 0; 
    let mut nearest_alpha_index_left = l-1;
    let mut found = false;

    // deduce rel list
    for seg_id in 0..=last {
        let (min, max) = if seg_id == 0 {
            // premier segment : (u_alpha[last] + 1 .. l)
            (u_alpha_view[last], l)
        } else {
            // ensuite : (u_alpha[last - seg_id] + 1 .. u_alpha[last - seg_id + 1])
            let ind_u = last - seg_id;
            (u_alpha_view[ind_u], u_alpha_view[ind_u + 1])
        };
        for t in min + 1..max {
            if d_ij_star_view[t] == w_ij_star_view[t] * h {
                first_true_from_right = t;
                found = true;
                nearest_alpha_index_right = min;
                nearest_alpha_index_left = max;
                for j in 0..=t {
                    rel_list_j_star[j] = (j == t);
                }
                break;
            }
        }
        if found{
            break;
        }
    }
    // println!("list real : {:?}", rel_list_j_star);
    // println!("First true from right: {}", first_true_from_right);
    // println!("Nearest alpha from right: {}", nearest_alpha_index_right);
    // println!("Nearest alpha from left: {}", nearest_alpha_index_left);
    // println!("alpha = {}", last);

    // generate the alea 
    for i in 0..l{
        if rel_list_j_star[i]{
            r_j_star[i] = random_scalar(rng_proof);
            rr_j_star[i] = r_j_star[i] * h;
        }else{
            u_j_star[i] = random_scalar(rng_proof);
        }
    }

    // if the first true is in the last parenthesis, simulate challenges for all the false term
    if first_true_from_right < u_alpha_view[1]{
        assert!(nearest_alpha_index_right == 0);
        for i in 0..l{
            if rel_list_j_star[i]==false{
                c_j_star[i] = random_scalar(rng_proof);
                rr_j_star[i] = w_ij_star_view[i] * h - c_j_star[i] * d_ij_star_view[i];
            }
        }
    }else{
        let mut buffer_sum = Scalar::ZERO;
        for i in 0..u_alpha_view[1]{
            let buffer = simulate_c_and_rr(
                i,
                &mut c_j_star, 
                &mut rr_j_star, 
                &d_ij_star_view, 
                &u_j_star, 
                h,
                rng_proof
            );
            buffer_sum += buffer;
        }
        c_j_star[u_alpha_view[1]] = buffer_sum;
        rr_j_star[u_alpha_view[1]] = u_j_star[u_alpha_view[1]] * h  - c_j_star[u_alpha_view[1]] * d_ij_star_view[u_alpha_view[1]];

        let mut end = 2;
        while u_alpha_view[end]<=nearest_alpha_index_right{
            buffer_sum = Scalar::ZERO;
            for i in u_alpha_view[end-1]+1..u_alpha_view[end]{
                let alea_c = simulate_c_and_rr(
                    i,
                    &mut c_j_star, 
                    &mut rr_j_star, 
                    &d_ij_star_view, 
                    &u_j_star, 
                    h,
                    rng_proof);
                buffer_sum += alea_c;
            }
            
            c_j_star[u_alpha_view[end]] = buffer_sum + c_j_star[u_alpha_view[end-1]];
            rr_j_star[u_alpha_view[end]] = u_j_star[u_alpha_view[end]] * h - c_j_star[u_alpha_view[end]] * d_ij_star_view[u_alpha_view[end]];
            end += 1;
        }
        // calculate the random for indices from index_right to index_left
        for i in nearest_alpha_index_right+1..nearest_alpha_index_left{
            if rel_list_j_star[i] == false{
                let _ = simulate_c_and_rr(
                    i,
                    &mut c_j_star, 
                    &mut rr_j_star, 
                    &d_ij_star_view, 
                    &u_j_star, 
                    h,
                    rng_proof);
            }
        }
        for i in nearest_alpha_index_left+1..l{
            if rel_list_j_star[i]==false{
                let _ = simulate_c_and_rr(
                    i,
                    &mut c_j_star, 
                    &mut rr_j_star, 
                    &d_ij_star_view, 
                    &u_j_star, 
                    h,
                    rng_proof);
            }
        }
    }

    // check if all the term has a rr replaced
    for i in 0..l{
        assert!(rr_j_star[i]!=RistrettoPoint::identity());
    }

    // calculate the challenges
    let mut rr : Vec<RistrettoPoint> = Vec::with_capacity(a*l);
    let mut y: Vec<RistrettoPoint> = Vec::with_capacity(a*l);
    for j in 0..a{
        if j==j_star{
            for rr_list_j_star in &rr_j_star{
                rr.push(*rr_list_j_star);
            }
        }else{
            if j < j_star{
                for rr_list in &simulate_proofs[j].commitments{
                    rr.push(*rr_list);
                }
            }else{
                for rr_list in &simulate_proofs[j-1].commitments{
                    rr.push(*rr_list);
                }
            }
        }
        for d_iju in &d_vec[j][offset..]{
                y.push(*d_iju);
            }
    }
    let chal = chal_list(&rr.clone(), &y, &vec![h;a*l]);

    // deduce chal_j_star
    let chal_j_star = chal - simulate_chal_sum;

    // calculate c and u for the term true for j_star
    if first_true_from_right > u_alpha_view[last]{
        println!("Entered in this block!"); // jamais ici
        let mut buffer = Scalar::ZERO;
        for i in u_alpha_view[last]..l{
            if i != first_true_from_right{
                buffer += c_j_star[i];
            }
        }
        c_j_star[first_true_from_right] = chal_j_star - buffer;
        u_j_star[first_true_from_right] = r_j_star[first_true_from_right] + c_j_star[first_true_from_right] * w_ij_star_view[first_true_from_right];
    }
    else{
        // println!("Relation at index 0: {:?}", rel_list_j_star[0]);
        let mut buffer = Scalar::ZERO;
        for i in u_alpha_view[last]+1..l{
            buffer += c_j_star[i];
        }
        c_j_star[u_alpha_view[last]] = chal_j_star - buffer;
        u_j_star[u_alpha_view[last]] = r_j_star[u_alpha_view[last]] + c_j_star[u_alpha_view[last]]*w_ij_star_view[u_alpha_view[last]];
        
        let mut end = last-1;
        while u_alpha_view[end] >= nearest_alpha_index_left{
            let mut sum = c_j_star[u_alpha_view[end+1]];
            for i in u_alpha_view[end]+1..u_alpha_view[end+1]{
                sum -= c_j_star[i];
            }
            c_j_star[u_alpha_view[end]] = sum;
            u_j_star[u_alpha_view[end]] = r_j_star[u_alpha_view[end]] + c_j_star[u_alpha_view[end]] * w_ij_star_view[u_alpha_view[end]];
            
            end -= 1;
        }
        
        buffer = c_j_star[nearest_alpha_index_left];
        for i in nearest_alpha_index_right..nearest_alpha_index_left{
            if i != first_true_from_right{
                buffer -= c_j_star[i]; 
            }
        }
        c_j_star[first_true_from_right] = buffer;
        u_j_star[first_true_from_right] = r_j_star[first_true_from_right] + c_j_star[first_true_from_right] * w_ij_star_view[first_true_from_right];
        
        for i in 0..l{
            assert!(u_j_star[i] != Scalar::ZERO);
        }
    }
    let proof_j_star = ZKthresholdi{commitments: rr_j_star, challenges: c_j_star, responses: u_j_star};
    let mut proofs : Vec<ZKthresholdi> = Vec::with_capacity(a);

    for j in 0..a{
        if j==j_star{
            proofs.push(proof_j_star.clone());
        }else{
            if j < j_star{
                proofs.push(simulate_proofs[j].clone());
            }else{
                proofs.push(simulate_proofs[j-1].clone());
            }
        }
    }

    return proofs;

}
// --- help function to put a random scalar into index ind for c 
// and calculate the rr
// and return the random value
pub fn simulate_c_and_rr<T: CryptoRngCore>(
    ind: usize,
    c: &mut Vec<Scalar>,
    rr: &mut Vec<RistrettoPoint>,
    d: &[RistrettoPoint],
    u: &[Scalar],
    h: RistrettoPoint,
    rng: &mut T
)->Scalar{
    // println!("simulate c and rr for index: {}", ind);
    let buffer = random_scalar(rng);
    c[ind] = buffer;
    rr[ind] = u[ind] * h - c[ind] * d[ind];
    return buffer;
}

// simulation proof for a given j
pub fn simulate_pi_1<T: CryptoRngCore>(
    u_alpha_view: &[usize],
    d_ij_view: &[RistrettoPoint], // binary
    h: RistrettoPoint,
    rng_proof: &mut T
)->(ZKthresholdi,Scalar){
    let l = d_ij_view.len();

    let mut c : Vec<Scalar> = vec![Scalar::ZERO; l]; // challenges
    let mut rr : Vec<RistrettoPoint> = Vec::with_capacity(l); // R
    // compute the responses
    let u : Vec<Scalar> = (0..l).map(|_| random_scalar(rng_proof)).collect(); // responses

    // compute c
    let alpha = u_alpha_view.len()-1;
    let mut begin : usize;
    let mut end : usize;
    let mut sum_buffer : Scalar;

    c[0] = random_scalar(rng_proof);
    for cursor in 0..alpha{
        begin = u_alpha_view[cursor]+1;
        end = u_alpha_view[cursor+1];
        sum_buffer = Scalar::ZERO;
        for k in begin..end{
            let buffer_ = random_scalar(rng_proof);
            c[k] = buffer_;
            sum_buffer += buffer_;
        }
        c[end] = (sum_buffer + c[begin-1]);
    }

    // calculate the challenge sum
    let mut sum_challenge = Scalar::ZERO;
    for i in u_alpha_view[alpha]+1..l{
        let buffer_ = random_scalar(rng_proof);
        c[i] = buffer_;
        sum_challenge += buffer_;
    }
    sum_challenge += c[u_alpha_view[alpha]];

    // compute the commitements R
    for i in 0..l{
        rr.push(u[i]*h - c[i]*d_ij_view[i]);
    }

    (ZKthresholdi{commitments: rr, challenges: c, responses: u}, sum_challenge)

}

pub fn verify_non_anomaly_j(
    proof: &ZKthresholdi, 
    y: Vec<RistrettoPoint>,
    h: RistrettoPoint,
    epsilon_bin: &[usize]) -> bool{
	
	// Parses the proof
	let rr = &proof.commitments;
	let c = &proof.challenges;
	let u = &proof.responses;

    let offset = epsilon_bin[0];

    let alpha = epsilon_bin[epsilon_bin.len()-1]-offset;
	
	let l = y.len()-offset;
	
	// Recomputes the general challenge
    let y_view = &y[offset..];  
	
	for b in 0..epsilon_bin.len() - 1 {
        let left = epsilon_bin[b] - offset;
        let right = epsilon_bin[b+1] - offset;
    
        let mut c_sum = Scalar::ZERO;
        for j in left..right {
            c_sum += c[j];
        }
    
        if c[right] != c_sum {
            println!("False , block {}", b);
            return false;
        }
    }

    for i in 0..l{
		if rr[i] != u[i] * h - c[i] * y_view[i]{
            println!("response verification failed for {}", i);
			return false	
		}
	}
	return true
}

pub fn verify_non_anomaly_i(
    proofs: Vec<ZKthresholdi>,
    u_alpha: &[usize],
    d_vec: &[&[RistrettoPoint]],
    h: RistrettoPoint
)->bool{
    let a = proofs.len();
    let offset = u_alpha[0];
    let u_alpha_view : Vec<usize> = u_alpha.iter().map(|val| val-offset).collect();
    let alpha = u_alpha_view[u_alpha_view.len()-1];
    let l = d_vec[0].len() - offset;

    let mut rr_aggregated : Vec<RistrettoPoint> = Vec::with_capacity(a*l);
    let mut y_aggregated : Vec<RistrettoPoint> = Vec::with_capacity(a*l);
    let mut chal_aggregated = Scalar::ZERO;

    let mut res : bool = true;

    for j in 0..a{
        let proof_j = &proofs[j];
        let rr_j = &proof_j.commitments;
        let c_j = &proof_j.challenges;
        // let u_j = proof_j.responses;
        let d_ij = d_vec[j];

        let verify_j = verify_non_anomaly_j(&proof_j, d_ij.to_vec(), h, u_alpha);

        res &= verify_j;

        // if verify_j == false{
        //     println!("Error in verify threshold i for j = {}", j);
        // }

        for i in alpha..l{
            chal_aggregated += c_j[i];
        }

        for rr in rr_j{
            rr_aggregated.push(rr.clone());
        }

        for y in d_ij{
            y_aggregated.push(y.clone());
        }
    }

    let chal = chal_list(&rr_aggregated.clone(), &y_aggregated.clone(), &vec![h; a*l]);

    res &= chal == chal_aggregated;

    res
}

pub fn measure_time_non_anomaly(
    upper: usize,
    n: usize,
    m: usize,
    ell: usize,
    iter: usize,
    epsilon: u64,
) -> (){
    let mut time_setup              = Duration::ZERO;
    let mut time_commit             = Duration::ZERO;
    let mut time_proof_non_anomaly     = Duration::ZERO;
    let mut time_verify_non_anomaly    = Duration::ZERO;

    for _ in 0..iter {
        // RNGs
        let mut rng = OsRng;
        let mut rng_k = OsRng;
        let mut rng_proof = OsRng;

        // --- Setup ---
        let t0 = Instant::now();
        let mut set = setup(n, &mut rng);
        time_setup += t0.elapsed();

        // --- Random TS ---
        let ts = random_ecg(&mut rng, n, upper);

        // --- Commit ---
        let c = commit(&mut set, &ts, &mut rng_k);
        
        let g = set.gen;
        let h = set.h_;

        let t1 = Instant::now();

        let (_, _, x_diff, k_diff, k_tilde) = calculate_inner_diff_commit(&c, &set, &mut rng_proof);
        
        let t1 = Instant::now();
        let (d_vec, _, w_vec, _) = calculate_dist_commit(&mut rng_proof, n, m, ell, g, h, &x_diff, &k_diff, &k_tilde);

        // calculate u_alpha list
        let epsilon_bin_val = scalar_to_bits(&Scalar::from(epsilon), ell);
        let mut epsilon_bin : Vec<usize> = Vec::with_capacity(ell);
        for bit in 0..epsilon_bin_val.len(){
            if epsilon_bin_val[bit] == Scalar::ZERO{
                epsilon_bin.push(bit);
            }
        }

        time_commit += t1.elapsed();

        let a = n - m + 1;
        let mut verify_non_anomaly : bool = true;
        for i in 0..a{
            // println!("==== i = {} ==== ", i);
            let d_i = &d_vec[i*a..i*a+a];
            let d_i_refs: Vec<&[RistrettoPoint]> = d_i.iter().map(|v| v.as_slice()).collect();
            let w_i = &w_vec[i*a..i*a+a];
            let w_i_refs: Vec<&[Scalar]> = w_i.iter().map(|v| v.as_slice()).collect();

            let t2 = Instant::now();
            let proof_i = prove_non_anomaly_i(&epsilon_bin, &d_i_refs, &w_i_refs, h, &mut rng_proof);
            time_proof_non_anomaly += t2.elapsed();

            let t3 = Instant::now();
            let res = verify_non_anomaly_i(proof_i, &epsilon_bin, &d_i_refs, h);
            verify_non_anomaly &= res;
            time_verify_non_anomaly += t3.elapsed();
        }
        println!("verify: {}", verify_non_anomaly);

    }
    let average_time_setup = time_setup / (iter as u32);
    let average_time_commit = time_commit / (iter as u32);
    let average_time_proof = time_proof_non_anomaly / (iter as u32);
    let average_time_verify = time_verify_non_anomaly / (iter as u32);
        
        
    println!("Average with n= {}, m = {}", n, m);
    print!("Setup: {:?} \n", average_time_setup);
    print!("Commit: {:?} \n", average_time_commit);
    print!("Proof: {:?} \n", average_time_proof);
    print!("Verify: {:?} \n", average_time_verify);

}