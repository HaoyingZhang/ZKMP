use rand::rngs::OsRng;
use rand_core::{ CryptoRng, RngCore, CryptoRngCore };   
use std::time::{ Instant, Duration }; 
use curve25519_dalek::{ scalar::Scalar, RistrettoPoint, traits::Identity};
use zeroize::Zeroize;
use crate::usefulstructs::*;
use crate::usefulfuncs::{random_ecg, random_ristretto_point, random_scalar, chal_single_proof_square, chal_distance, random_vec_scalar, lincomb_pow2, two_pow, scalar_to_bits, compute_mpd_with_window_scalar, chal_list};

use crate::commit::*;
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
        let (c_vec, c_bis_vec, w, _, _) = calculate_dist_commit(&mut rng_proof, n, m, u, g, h, &x_diff, &k_diff, &k_tilde);
        
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