use rand::rngs::OsRng;
use rand_core::{ CryptoRng, RngCore, CryptoRngCore };   
use std::time::{ Instant, Duration }; 
use curve25519_dalek::{ scalar::Scalar, RistrettoPoint, traits::Identity};
use zeroize::Zeroize;
use crate::usefulstructs::*;
use crate::usefulfuncs::{random_ecg, random_ristretto_point, random_scalar, chal_single_proof_square, chal_distance, random_vec_scalar, lincomb_pow2, two_pow, scalar_to_bits, compute_mpd_with_window_scalar, chal_list};

use crate::commit::*;

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
