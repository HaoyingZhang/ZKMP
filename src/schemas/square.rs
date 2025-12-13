use rand::rngs::OsRng;
use rand_core::{ CryptoRng, RngCore, CryptoRngCore };   
use std::time::{ Instant, Duration }; 
use curve25519_dalek::{ scalar::Scalar, RistrettoPoint, traits::Identity};
use zeroize::Zeroize;
use crate::usefulstructs::*;
use crate::usefulfuncs::{random_ecg, random_ristretto_point, random_scalar, chal_single_proof_square, chal_distance, random_vec_scalar, lincomb_pow2, two_pow, scalar_to_bits, compute_mpd_with_window_scalar, chal_list};

use crate::commit::*;
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
        
        // ----------- General commit -------------- //
        let c: Commit = commit(&mut set, &ts, &mut rng_k); // commit of device
        let start_commit = Instant::now();
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