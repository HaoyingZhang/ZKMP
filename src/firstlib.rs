#[allow(unused_imports)]
#[allow(unused_variables)]
use rand::rngs::OsRng;
use rand_core::{ CryptoRng, RngCore, CryptoRngCore };   
use std::time::{ Instant, Duration }; 
use curve25519_dalek::{ scalar::Scalar, RistrettoPoint, traits::Identity, constants::RISTRETTO_BASEPOINT_POINT, constants::RISTRETTO_BASEPOINT_TABLE };
use zeroize::Zeroize;
use sha2::{ Sha512, Digest }; 
use std::io;
use std::io::{ IoSlice, Write };
use std::fs::File;
use std::fs;
use std::io::Read;
use curve25519_dalek::ristretto::CompressedRistretto;
use crate::usefulstructs::*;
use crate::usefulfuncs::{random_ristretto_point, random_scalar, chal_single_proof_square, chal_distance, random_vec_scalar, lincomb_pow2, two_pow, scalar_to_bits, compute_mpd_with_window_scalar, chal_list};
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

    let g = set.gen;
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

pub fn measure_time_proof_square(
    ts: &Vec<Scalar>,
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

        // Commit:
        let start_commit = Instant::now();
        // ----------- General commit -------------- //
        let c: Commit = commit(&mut set, ts, &mut rng_k); // commit of device

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
    let g = set.gen;       // RistrettoPoint
    let h = set.h_;        // RistrettoPoint

    // Commitment for this bit
    let mut r1: RistrettoPoint = RistrettoPoint::identity();
    let mut r2: RistrettoPoint = RistrettoPoint::identity();
    let mut c1: Scalar = Scalar::ZERO;
    let mut c2: Scalar = Scalar::ZERO;
    let mut z1: Scalar = Scalar::ZERO;
    let mut z2: Scalar = Scalar::ZERO;
    let mut c_chal: Scalar = Scalar::ZERO; 

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

    let g = set.gen;
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
    ts: &Vec<Scalar>,
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

        // --- Commit ---
        let t1 = Instant::now();
        let c = commit(&mut set, ts, &mut rng_k);

        // Computation of the local commitments
        let l = n - m + 1;
        
        let g = set.gen;
        let h = set.h_;

        let (c_diff, c_tilde, x_diff, k_diff, k_tilde) = calculate_inner_diff_commit(&c, &set, &mut rng_proof);
        
        let mut c_vec : Vec<Vec<RistrettoPoint>> = Vec::with_capacity(l*l);
        let mut c_bis_vec : Vec<Vec<RistrettoPoint>> = Vec::with_capacity(l*l);
        let mut w : Vec<Vec<Scalar>> = Vec::with_capacity(l*l);

        for i in 0..l{
            for j in 0..l{
                let mut wij = Scalar::ZERO;
                let mut dij = Scalar::ZERO;

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
                    wij_pub.push(random_scalar(&mut rng_proof));
                }
                let first = lincomb_pow2(&wij_pub);
                let denom = two_pow(u - 1); // 2^(u-1)
                let last = (wij - first) * denom.invert(); // division with scalar
                wij_pub.push(last);

                let d_ij_vec: Vec<RistrettoPoint> = dij_bin.iter().zip(wij_pub.iter()).map(|(dij, wij)| dij * g + wij * h).collect();
                let d_ij_bis_vec: Vec<RistrettoPoint> = d_ij_vec.iter().map(|d_ij| d_ij - g).collect();
                
                c_vec.push(d_ij_vec);
                c_bis_vec.push(d_ij_bis_vec);
                w.push(wij_pub); // push the wiju list
            }
        }
        
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

// -----------------------------------------------------------

pub fn proof_mpd_bin_iu<T: CryptoRng + RngCore>(
    mpd_iu: Scalar,      // public bit (0 or 1)
    ziu: Scalar,         // witness for generator h
    set: &Set,
    rng_proof: &mut T,
) -> ProofMPDBiniu {
    let g = set.gen;
    let h = set.h_;

    let m_iu      = g * mpd_iu + h * ziu;
    let m_iu_bis  = m_iu - g;         

    // Pre-init to avoid shadowing
    let mut r1: RistrettoPoint = RistrettoPoint::identity();
    let mut r2: RistrettoPoint = RistrettoPoint::identity();
    let mut c1: Scalar = Scalar::ZERO;
    let mut c2: Scalar = Scalar::ZERO;
    let mut z1: Scalar = Scalar::ZERO;
    let mut z2: Scalar = Scalar::ZERO;

    // Choose which half to simulate based on whether the bit is 0 or 1
    if m_iu == h * ziu {
        // mpd_iu == 0 branch (simulate the other half)
        let r = random_scalar(rng_proof);
        r1 = h * r;

        z2 = random_scalar(rng_proof);
        c2 = random_scalar(rng_proof);
        r2 = h * z2 - c2 * m_iu;

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
    set: &Set,
    mpd_i_bin: &[Scalar],          // length u, bits in {0,1} as Scalars
    u: usize,
    rng_proof: &mut T,
) -> (Vec<ProofMPDBiniu>, Vec<RistrettoPoint>) {
    let g = set.gen;
    let h = set.h_;                // <-- fixed

    // fresh witnesses per bit
    let mut zi_pub: Vec<Scalar> = (0..u).map(|_| random_scalar(rng_proof)).collect();

    let mut mpd_i_commit: Vec<RistrettoPoint> = Vec::with_capacity(u);
    let mut proof_mpd_i:  Vec<ProofMPDBiniu>   = Vec::with_capacity(u);

    for bit in 0..u {
        let c_u = g * mpd_i_bin[bit] + h * zi_pub[bit];
        mpd_i_commit.push(c_u);

        // ZK proof of knowledge of zi_pub[bit] consistent with C_u
        let proof = proof_mpd_bin_iu(mpd_i_bin[bit], zi_pub[bit], set, rng_proof);
        proof_mpd_i.push(proof);
    }

    (proof_mpd_i, mpd_i_commit)
}


pub fn verify_MPD_bin_i(
    m_i: &[RistrettoPoint],          // commitments per bit
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
    mpd_bin: &[&[Scalar]],            // length w, each is length u bits
    n: usize,
    m: usize,
    u: usize,
    set: &Set,
    rng_proof: &mut T,
) -> (Vec<Option<Vec<ProofMPDBiniu>>>, Vec<Option<Vec<RistrettoPoint>>>) {
    let w = n - m + 1;

    let mut proofs: Vec<Option<Vec<ProofMPDBiniu>>> = Vec::with_capacity(w);
    let mut commits: Vec<Option<Vec<RistrettoPoint>>> = Vec::with_capacity(w);

    for i in 0..w {
        let (p_i, m_i) = proof_mpd_bin_i(set, mpd_bin[i], u, rng_proof);
        proofs.push(Some(p_i));
        commits.push(Some(m_i));
    }
    (proofs, commits)
}

pub fn verify_MPD_bin(
    n: usize,
    m: usize,
    _commitment: &Commit,
    commits_opt: &[Option<&[RistrettoPoint]>],
    set: &Set,
    proofs_opt: &[Option<&[ProofMPDBiniu]>],
) -> bool {
    let w = n - m + 1;
    debug_assert_eq!(commits_opt.len(), w);
    debug_assert_eq!(proofs_opt.len(),  w);

    let mut res = true;
    for i in 0..w {
        match (commits_opt[i], proofs_opt[i]) {
            (Some(commits_i), Some(proofs_i)) => {
                res &= verify_MPD_bin_i(commits_i, set, proofs_i);
            }
            _ => { /* if you ever store None, mirror it here */ }
        }
    }
    res
}

pub fn measure_time_proof_MPD(
    ts: &[Scalar],
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

        // Compute MPD and bit-decompose (u bits per index)
        let mpd      = compute_mpd_with_window_scalar(&ts, m);
        let mpd_binv: Vec<Vec<Scalar>> = mpd.iter().map(|x| scalar_to_bits(x, u)).collect();
        let mpd_bin:  Vec<&[Scalar]>   = mpd_binv.iter().map(|v| v.as_slice()).collect();

        // Setup
        let t0 = Instant::now();
        let mut set = setup(n, &mut rng);
        time_setup += t0.elapsed();

        // Commit (not used by these MPD proofs but kept for parity)
        let t1 = Instant::now();
        let c = commit(&mut set, &ts.to_vec(), &mut rng_k);
        time_commit += t1.elapsed();

        // Prove MPD bits
        let t2 = Instant::now();
        let (proofs_owned, commits_owned) = proof_MPD_bin(&mpd_bin, n, m, u, &set, &mut rng_proof);
        time_proof_mpd += t2.elapsed();

        // Borrow for verify
        let commits_borrowed: Vec<Option<&[RistrettoPoint]>> =
            commits_owned.iter().map(|opt| opt.as_deref()).collect();
        let proofs_borrowed: Vec<Option<&[ProofMPDBiniu]>> =
            proofs_owned.iter().map(|opt| opt.as_deref()).collect();

        // Verify
        let t3 = Instant::now();
        let ok = verify_MPD_bin(n, m, &c, &commits_borrowed, &set, &proofs_borrowed);
        time_verify_mpd += t3.elapsed();

        debug_assert!(ok, "MPD bit proof failed verification");
    }

    let it = iter as u32;
    println!("Average with n = {}, m = {}, u = {}", n, m, u);
    println!("Setup:   {:?}", time_setup  / it);
    println!("Commit:  {:?}", time_commit / it);
    println!("Proof:   {:?}", time_proof_mpd / it);
    println!("Verify:  {:?}", time_verify_mpd / it);
}

// ----------------------
pub fn proof_exist_bin<T: CryptoRng + RngCore>(
    set: &Set,
    l: usize,                  // length in bits
    a: usize,                  // length of matrix profile
    m_i: &[RistrettoPoint],    // Pedersen commitments of MPD_i bits
    d_ij: &[RistrettoPoint],   // Pedersen commitments of distances s_i and s_j (flattened: a * l)
    z_i: &[Scalar],            // openings for m_i
    w_ij: &[Scalar],           // openings for d_ij (flattened: a * l)
    rng_proof: &mut T,
) -> ProofExistij {
    // --- Basic sanity checks ---
    debug_assert_eq!(m_i.len(), l, "m_i must have length l");
    debug_assert_eq!(z_i.len(), l, "z_i must have length l");
    debug_assert_eq!(d_ij.len(), a * l, "d_ij must have length a * l");
    debug_assert_eq!(w_ij.len(), a * l, "w_ij must have length a * l");

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
            let alpha_u = z_i[u] - w_ij[j * l + u];
            let y_u     = m_i[u] - d_ij[j * l + u];

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
                let alpha_u = z_i[u] - w_ij[j * l + u];
                let y_u     = m_i[u] - d_ij[j * l + u];

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
                let alpha_u = z_i[u] - w_ij[j * l + u];
                let y_u     = m_i[u] - d_ij[j * l + u];

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
        let alpha_u      = z_i[u] - w_ij[index_j_star * l + u];
        let res_j_star_u = alea_buffer[u] + alpha_u * c_j_star;
        res_i[index_j_star * l + u] = res_j_star_u;
    }
    return ProofExistij{r_i: r_i, c_i: c_i, z_i:res_i}
}

pub fn verify_exist_bin(
    m_i: &[RistrettoPoint],
    d_ij: &[RistrettoPoint],
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
            let y_u = m_i[u] - d_ij[j*l+u];
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
    x: &[Scalar],
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
        let mut rng_dist   = OsRng;

        // --- Compute MPD and bit-decompose (u bits per index) ---
        let ts = x; // alias
        let mpd = compute_mpd_with_window_scalar(ts, m);
        let mpd_binv: Vec<Vec<Scalar>> = mpd.iter().map(|val| scalar_to_bits(val, u)).collect();
        let mpd_bin: Vec<&[Scalar]> = mpd_binv.iter().map(|v| v.as_slice()).collect();

        let k_tilde = random_vec_scalar(&mut rng, n * n);

        // --- Setup ---
        let t0 = Instant::now();
        let mut set = setup(n, &mut rng);
        time_setup += t0.elapsed();

        // --- Commit (kept for parity) ---
        let t1 = Instant::now();
        let commitment = commit(&mut set, &ts.to_vec(), &mut rng_k);
        time_commit += t1.elapsed();

        // Per-iteration accumulated time for all i
        let mut time_proof_iter  = Duration::ZERO;
        let mut time_verify_iter = Duration::ZERO;

        let x = &commitment.x_;
        let k = &commitment.k_;
        let n = set.n_;
        let g = set.gen;
        let h = set.h_;

        // --- For each i: build commitments and run proof/verify ---
        for i in 0..a {
            // M_i = Com(mpd_i in binary)
            let mpd_i_bin = mpd_bin[i]; // length u

            // public randomness for M_i
            let zi_pub: Vec<Scalar> = (0..u).map(|_| random_scalar(&mut rng_proof)).collect();

            let m_i: Vec<RistrettoPoint> = (0..u).map(|bit| g * mpd_i_bin[bit] + h * zi_pub[bit]).collect();

            let mut d_ij: Vec<RistrettoPoint> = Vec::with_capacity(a * u);
            let mut w_ij: Vec<Scalar>         = Vec::with_capacity(a * u);

            for j in 0..a {
                let mut wij_private = Scalar::ZERO;
                let mut dij_private = Scalar::ZERO;
            
                // compute distance and masked distance between subsequences
                for r in 0..m {
                    let xij = x[i + r] - x[j + r];
                    let kij = k[i + r] - k[j + r];
                    let k_tilde_ij = k_tilde[(i + r) * n + (j + r)];
            
                    wij_private += xij * kij + k_tilde_ij;
                    dij_private += xij * xij;
                }
            
                // dij in binary (u bits, Scalars 0/1)
                let dij_bin = scalar_to_bits(&dij_private, u);
            
                // sample u-1 random public shares for wij and set the last to match sum
                let mut wij_pub: Vec<Scalar> = Vec::with_capacity(u);
                for _ in 0..(u - 1) {
                    wij_pub.push(random_scalar(&mut rng_dist));
                }
            
                let first = lincomb_pow2(&wij_pub);   // sum_{b=0..u-2} wij_pub[b] * 2^b
                let denom = two_pow(u - 1);          // 2^(u-1)
                let last  = (wij_private - first) * denom.invert();
                wij_pub.push(last);                  // length u
            
                for share in &wij_pub {
                    w_ij.push(*share);
                }
            
                // commitments for each bit of dij using wij_pub as openings
                let d_ij_commit: Vec<RistrettoPoint> = (0..u).map(|bit| dij_bin[bit] * g + wij_pub[bit] * h).collect();
            
                for dij in d_ij_commit {
                    d_ij.push(dij);
                }
            }

            // --- Proof ---
            let t_proof = Instant::now();
            let proof_existence = proof_exist_bin(
                &set,
                u,     
                a,
                &m_i,
                &d_ij,
                &zi_pub,
                &w_ij,
                &mut rng_proof,
            );
            time_proof_iter += t_proof.elapsed();

            // --- Verify ---
            let t_verify = Instant::now();
            let res = verify_exist_bin(&m_i, &d_ij, u, a, &set, &proof_existence);
            time_verify_iter += t_verify.elapsed();

            println!("{:?}", res);
            debug_assert!(res, "verify_exist_bin failed for i = {}", i);
        }

        // accumulate over all iterations
        time_proof_mpd  += time_proof_iter;
        time_verify_mpd += time_verify_iter;
    }

    println!("Total over {} iterations:", iter);
    println!("  setup:        {:?}", time_setup);
    println!("  commit:       {:?}", time_commit);
    println!("  proof (MPD):  {:?}", time_proof_mpd);
    println!("  verify (MPD): {:?}", time_verify_mpd);
}

// --------------------------
pub fn list_relation(
    mut cmpt: usize,
    mpd_bin: Vec<Scalar>,
    d_ij: Vec<Scalar>,
    mut found: bool,
    mut list: Vec<bool>
) -> Vec<bool>{
	while (found == false) && (cmpt > 0){
		if d_ij[cmpt-1] - mpd_bin[cmpt-1] == Scalar::ONE {
			list[2*cmpt-1] = true; // corresponds to y_{2l}
			found = true;
		}
		else{
			list[2*cmpt-2] = true; // corresponds to y_{2l-1}	
			cmpt = cmpt - 1;
			list_relation(cmpt,mpd_bin.clone(),d_ij.clone(),found,list.clone());
		}
	}
    // println!("cmpt = {}", cmpt);
	return list;
}

pub fn prove_min<T: CryptoRng + RngCore>(rng: &mut T, y: Vec<RistrettoPoint>,h: RistrettoPoint,mut alpha: Vec<Scalar>,mut list: Vec<bool>) -> ZKmin{
	let l = y.len() / 2;
	let mut r: Vec<Scalar> = vec![Scalar::from(0u64);2*l]; // vector of random 
	let mut rr: Vec<RistrettoPoint> = vec![RistrettoPoint::identity();2*l]; // vector of commitments
	let mut c: Vec<Scalar> = vec![Scalar::from(0u64);2*l]; // vector of challenges
	let mut u: Vec<Scalar> = vec![Scalar::from(0u64);2*l]; // vector of responses
	
	let mut first = 0;
	while list[first] == false{
		first +=1;
	}
	
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
	
	alpha.zeroize();
	r.zeroize();
	list.zeroize();
	
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
		return false
	}
	for i in 0..2*l-1{
		if rr[i] != u[i] * h - c[i] * y[i]{
			return false	
		}
	}
	
	for i in 2..l{
		if c[2*i-2] != c[2*i-3] + c[2*i-4]{
			println!("{:?}, {}",c[2*i-2] == c[2*i-3] + c[2*i-4],i);
			return false
		}
	}
	return true
}


pub fn proof_mpd_min<T: CryptoRngCore>(
    mpd_bin: Vec<Vec<Scalar>>, // [MPD_i_binary]
    d_ij: Vec<Vec<Scalar>>, // [d_i_j_binary]
    h: &RistrettoPoint,
    l: usize, // l = n-m+1, length of MPD
    _k: usize,
    m: usize,
    alpha_list: &[Vec<Scalar>], // list of secrets
    y_list: &[Vec<RistrettoPoint>], // list of commitments
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

                let mut list = vec![false;rels];
                let cmpt = k_local;
                let found = false;

                // let t_list = Instant::now();
    	        let list = list_relation(cmpt, mpd_bin[i].clone(), d_ij[i*l+j].clone(), found, list);
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
    x: &[Scalar],
    n: usize,   // length of time series
    m: usize,   // window size
    ell: usize, // number of bits (ℓ)
    iter: usize,
) {
    let a = n - m + 1; // number of MPD entries (indices i ∈ I

    let mut time_setup      = Duration::ZERO;
    let mut time_commit     = Duration::ZERO;
    let mut time_proof_mpd  = Duration::ZERO;
    let mut time_verify_mpd = Duration::ZERO;

    for _ in 0..iter {
        let mut rng       = OsRng;
        let mut rng_k     = OsRng;
        let mut rng_proof = OsRng;
        let mut rng_dist  = OsRng;

        // --- 1) Compute MPD(i) for each i -------------------------------
        let ts = x; // alias
        let mpd = compute_mpd_with_window_scalar(ts, m); // length a

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
        let n_set = set.n_;

        // --- 3) Commit original time series (for distances etc.) --------
        let t1 = Instant::now();
        let commitment = commit(&mut set, &ts.to_vec(), &mut rng_k);

        let x_enc = &commitment.x_;
        let k_enc = &commitment.k_;

        // --- 4) Build MPD bit commitments M_{i,u} and store z_{i,u} -----
        //
        // M_{i,u} = g^{MPD_{i,u}} h^{z_{i,u}}
        // z_{i,u} random scalar
        //
        let mut M_list: Vec<Vec<RistrettoPoint>> = Vec::with_capacity(a);
        let mut z_list: Vec<Vec<Scalar>>         = Vec::with_capacity(a); // z_{i,u}
        let mut d_bits: Vec<Vec<Scalar>>         = Vec::with_capacity(a);

        for i in 0..a {
            let mut M_i: Vec<RistrettoPoint> = Vec::with_capacity(ell);
            let mut zi: Vec<Scalar>         = Vec::with_capacity(ell);

            for u_idx in 0..ell {
                let bit = mpd_bits[i][u_idx];         // MPD_{i,u} ∈ {0,1}
                let z_iu = random_scalar(&mut rng_proof); // z_{i,u} ∈ Z_p
                let M_iu = g * bit + h * z_iu;        // Pedersen-like commitment

                M_i.push(M_iu);
                zi.push(z_iu);
            }

            M_list.push(M_i);
            z_list.push(zi);
        }

        // --- 5) Build y_list and alpha_list for the MIN proof -----------
        //
        // For each pair (i,j) and each bit u:
        //  - compute distance d_{i,j},
        //  - derive some commitment using randomness w_{i,j,u},
        //  - define α_{i,j,u} = z_{i,u} - w_{i,j,u}.
        //
        // Here we’ll use:
        //   D_{i,j,u} = g^{d_{i,j,u}} h^{w_{i,j,u}}
        // then Y_{i,j,u} is something like:
        //   Y_{i,j,u} = M_{i,u} / D_{i,j,u} for impair terms and Y_{i,j,u} = g * M_{i,u} / D_{i,j,u} for pair terms
        //
        //
        let mut y_list: Vec<Vec<RistrettoPoint>>  = Vec::with_capacity(a * a);
        let mut alpha_list: Vec<Vec<Scalar>>      = Vec::with_capacity(a * a);
        let k_tilde = random_vec_scalar(&mut rng, n * n);

        for i in 0..a {
            let zi = &z_list[i];    // length ell
            let Mi = &M_list[i];    // length ell

            for j in 0..a {
                // --- distance d_{i,j} in scalar form -------------------
                let mut d_ij = Scalar::ZERO;
                let mut wij_private = Scalar::ZERO;

                for r in 0..m {
                    let xij = x[i + r] - x[j + r];
                    let kij = k_enc[i + r] - k_enc[j + r];
                    let k_tilde_ij = k_tilde[(i + r) * n + (j + r)];
            
                    wij_private += xij * kij + k_tilde_ij;
                    d_ij += xij * xij;
                }

                // binary bits of d_{i,j}
                let d_ij_bits = scalar_to_bits(&d_ij, ell); // length ell
                d_bits.push(d_ij_bits.clone());

                // randomness w_{i,j,u} for each bit (public shares)
                let mut w_ij_vec: Vec<Scalar> = Vec::with_capacity(ell);
                for _ in 0..ell-1 {
                    w_ij_vec.push(random_scalar(&mut rng_dist));
                }
            
                let first = lincomb_pow2(&w_ij_vec);   // sum_{b=0..u-2} wij_pub[b] * 2^b
                let denom = two_pow(ell - 1);          // 2^(u-1)
                let last  = (wij_private - first) * denom.invert();
                w_ij_vec.push(last); 

                // commitments D_{i,j,u} = g^{d_{i,j,u}} h^{w_{i,j,u}}
                let mut D_ij: Vec<RistrettoPoint> = Vec::with_capacity(ell);
                for u_idx in 0..ell {
                    let bit_d = d_ij_bits[u_idx];
                    let w_ij = w_ij_vec[u_idx];

                    let D_ij_u = g * bit_d + h * w_ij;
                    D_ij.push(D_ij_u);
                }

                // define Y_{i,j,u} = M_{i,u} - D_{i,j,u}  (i.e., group division)
                // so that:
                //   Y_{i,j,u} = g^{MPD_{i,u} - d_{i,j,u}} h^{z_{i,u} - w_{i,j,u}}
                // and the witness α_{i,j,u} for the h-part is:
                //   α_{i,j,u} = z_{i,u} - w_{i,j,u}
                //
                // This matches what your `prove_min` expects: y = h^{α} (up to
                // how you encode the g-part / bit tests in your AND/OR tree).
                //
                let mut Y_ij: Vec<RistrettoPoint> = Vec::with_capacity(ell);
                let mut alpha_ij: Vec<Scalar>     = Vec::with_capacity(ell);

                for u_idx in 0..ell {
                    let z_iu  = zi[u_idx];
                    let w_iju = w_ij_vec[u_idx];

                    let alpha_iju = z_iu - w_iju;     // *** here: α = z - w ***
                    alpha_ij.push(alpha_iju);
                    alpha_ij.push(alpha_iju);

                    let M_iu = Mi[u_idx];
                    let D_ij_u = D_ij[u_idx];

                    let Y_ij_u = M_iu - D_ij_u;
                    Y_ij.push(Y_ij_u); // y_pair
                    Y_ij.push(Y_ij_u + g); //y_impair
                }

                y_list.push(Y_ij);
                alpha_list.push(alpha_ij);
            }
        }
        time_commit += t1.elapsed();

        println!("  commit:        {:?}", time_commit);

        // initiate is_real_relation list
        let is_real_relation = vec![false; 2 * ell];

        // --- 6) PROOF time ----------------------------------------------
        let t_proof = Instant::now();
        let proof_list = proof_mpd_min(
            mpd_bits,
            d_bits,
            &h,
            a,              // l = number of indices
            ell,            // k = number of bits per index (or your tree depth parameter)
            m,            
            &alpha_list,
            &y_list,
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
    println!("l = {}", l);
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
    for ind in (epsilon_bin[last]-offset+1..l){
        println!("{}", ind);
        if y_view[ind] == alpha_view[ind] * h{
            println!("enter in the first or");
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
                    list_relation[min] = false;
                    break;
                }
            }
        }
    }

    println!("{:?}", list_relation);
    // deduce the first true relation from right
    while(list_relation[first]==false){
        first+=1;
    }
    // generate vlidation list for epsilon_bin
    let mut list_epsilon_bool : Vec<bool> = vec![false; l];
    for bit in epsilon_bin{
        list_epsilon_bool[bit-offset] = true;
    }


    // commitment phase
    for i in 0..l{
        if (list_relation[i]){
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
            if (list_relation[i]==false){
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

pub fn verify_threshold<T: CryptoRngCore>(
    h: &RistrettoPoint,
    y_list: &[Vec<RistrettoPoint>],
    proof_rng: &mut T,
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
    x: &[Scalar],
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
        let mut rng_dist  = OsRng;

        // --- 1) Compute MPD(i) for each i -------------------------------
        let ts = x; // alias
        let mpd = compute_mpd_with_window_scalar(ts, m); // length a
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
        let n_set = set.n_;

        // --- 3) Commit original time series (for distances etc.) --------
        let t1 = Instant::now();
        let commitment = commit(&mut set, &ts.to_vec(), &mut rng_k);

        let x_enc = &commitment.x_;
        let k_enc = &commitment.k_;

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
        println!("{:?}", epsilon_bin);

        time_commit += t1.elapsed();

        println!("  commit:        {:?}", time_commit);

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

        println!("  proof (MIN):   {:?}", time_proof_threshold);

        // --- 7) VERIFY time ---------------------------------------------
        let t_verify = Instant::now();
        let ok = verify_threshold(
            &h,
            &Y_list,
            &mut rng_proof,
            &proof_list,
            &epsilon_bin
        );

        time_verify_threshold += t_verify.elapsed();
        println!("  verify (THRESHOLD):  {:?}", time_verify_threshold);

        println!("{:?}",ok);
        debug_assert!(ok, "verify_threshold failed!");
    }

    println!("==== THRESHOLD timing over {} iterations ====", iter);
    println!("  setup:         {:?}", time_setup/(iter as u32));
    println!("  commit:        {:?}", time_commit/(iter as u32));
    println!("  proof (MIN):   {:?}", time_proof_threshold/(iter as u32));
    println!("  verify (MIN):  {:?}", time_verify_threshold/(iter as u32));
}