use rand::rngs::OsRng;
use rand_core::{ CryptoRng, RngCore, CryptoRngCore };   
use std::time::{ Instant, Duration }; 
use curve25519_dalek::{ scalar::Scalar, RistrettoPoint, traits::Identity};
use zeroize::Zeroize;
use crate::usefulstructs::*;
use crate::usefulfuncs::{random_ecg, random_ristretto_point, random_scalar, chal_proof_extraction, chal_distance, random_vec_scalar, lincomb_pow2, two_pow, scalar_to_bits, compute_mpd_with_window_scalar, chal_list};

use crate::commit::*;
// ------ Proof of square of distance for subsequences si and sj ------
// The proof takes the secret x_ij, the private key k_ij, k_ij_tilde the public key c_ij, c_ij_tilde 
pub fn proof_extract<T: CryptoRng + RngCore>(
    x_i: Scalar,
    k_i: Scalar,
    c_i: &RistrettoPoint,
    set: &Set,
    rng_proof: &mut T,
) -> ProofExtraction {
    // generators
    let g = set.gen;
    let h = set.h_;

    // randomness
    let s = random_scalar(rng_proof);
    let r = random_scalar(rng_proof);

    // public elements
    let rr = r * g;
    let ss = s * h;

    // challenge
    let c_chal = chal_proof_extraction(&rr, &ss, &c_i, &g, &h);

    // responses
    let u = r + x_i * c_chal;
    let v = s + k_i * c_chal;

    let proof = ProofExtraction {
        r_1: rr,
        s_1: ss,
        u: u,
        v: v
    };

    return proof
}

// ------ verify proof square ij ------
// calculate the challenge from the elements in the proof, and verify pi_square_i_j
pub fn verify_extract(
    c_ij: &RistrettoPoint,
    set: &Set, 
    proof_extract: &ProofExtraction
)-> bool{
    let g = set.gen;
    let h = set.h_;
    let r1 = &proof_extract.r_1;
    let s1 = &proof_extract.s_1;
    let u = &proof_extract.u;
    let v = &proof_extract.v;

    let c_verify = chal_proof_extraction(&r1, &s1, &c_ij, &g, &h);

    if (u*g+v*h != r1+s1+c_verify*c_ij) {
    	return false;
    } 
    return true;
}

pub fn measure_time_proof_extraction(
    upper: usize,
    n: usize,
    m: usize, 
    iter: usize
){
    let mut time_setup = Duration::ZERO;
    let mut time_commit = Duration::ZERO;
    let mut time_proof = Duration::ZERO;
    let mut time_verify = Duration::ZERO;

    let mut rng = OsRng; 
    let mut rng_k = OsRng;
    let mut rng_proof_square = OsRng;
    // Setup:
    for _ in 0..iter{
        let start_setup = Instant::now();
        let mut set: Set = setup(n, &mut rng);
        let duration_setup = start_setup.elapsed();
        time_setup = time_setup + duration_setup;

        let ts = random_ecg(&mut rng, n, upper);

        // Commit:
            
        // ----------- General commit -------------- //
        let start_commit = Instant::now();
        let c: Commit = commit(&mut set, &ts, &mut rng_k); // commit of device
        
        let duration_commit = start_commit.elapsed();
        time_commit = time_commit + duration_commit;


        // Proof square :
        let x_i = c.x_[0];
        let c_i = c.c_[0];
        let k_i = c.k_[0];
        let start_proof = Instant::now();
        let p = proof_extract(
            x_i,
            k_i,
            &c_i, 
            &set,
            &mut rng_proof_square
        );

        let duration_proof = start_proof.elapsed();
        time_proof += duration_proof;
            
        // Verify proof of square :
        let start_verify = Instant::now();
        let res = verify_extract(
            &c_i,
            &set, 
            &p
        );
        let duration_verify = start_verify.elapsed();
        time_verify += duration_verify;

        println!("Verify: {}", res);
        debug_assert!(res, "square proof failed verification"); 
    }
    
    let average_time_setup = time_setup / (iter as u32);
    let average_time_commit = time_commit / (iter as u32);
    let average_time_proof = time_proof / (iter as u32);
    let average_time_verify = time_verify / (iter as u32);
        
        
    println!("Average with n= {}, m = {}", n, m);
    print!("Setup: {:?} \n", average_time_setup);
    print!("Commit: {:?} \n", average_time_commit);
    print!("Proof: {:?} \n", average_time_proof);
    print!("Verify: {:?} \n", average_time_verify);
}