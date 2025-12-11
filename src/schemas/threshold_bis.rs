use curve25519_dalek::{ scalar::Scalar, RistrettoPoint, traits::Identity};
use crate::comp_bis::{simulate_pi_0, scalar_to_u64};
use rand_core::{ CryptoRng, RngCore, CryptoRngCore, OsRng };  
use crate::comp::{simulate_c_and_rr};
use crate::usefulstructs::*;
use crate::usefulfuncs::{random_ecg, random_ristretto_point, random_scalar, chal_single_proof_square, chal_distance, random_vec_scalar, lincomb_pow2, two_pow, scalar_to_bits, compute_mpd_with_window_scalar, chal_list};
use std::time::{ Instant, Duration }; 

use crate::square::*;        
use crate::distance::*;  
use crate::mpd_bin::*;  
use crate::mpd_exist::*;
use crate::mpd_min::*;
use crate::threshold::*;
use crate::comp::*;
use crate::commit::*;


// we can use the distance value to find ij
pub fn find_mpd_i_bigger_than_threshold(mpd: Vec<Scalar>, threshold: Scalar, a: usize)->usize{
    let thr = scalar_to_u64(threshold);

    for i in 0..mpd.len() {
        let value = scalar_to_u64(mpd[i].clone());
        if value > thr {
            return i;
        }
    }

    println!("WARNING: No distance bigger than the threshold!");
    0
}

pub fn prove_comp_anomaly<T: CryptoRngCore>(
    threshold: Scalar,
    mpd_vec_bin: Vec<Scalar>,
    n: usize,
    m: usize,
    u: usize,
    m_bis_vec: &[&[RistrettoPoint]],
    z_vec:  &[&[Scalar]],
    h: RistrettoPoint,
    rng_proof: &mut T
)->Vec<ZKthresholdi>{
    let a = n-m+1;
    assert_eq!(mpd_vec_bin.len(),a);
    let epsilon_bin_val = scalar_to_bits(&Scalar::from(threshold), u);
    let mut u_alpha : Vec<usize> = Vec::with_capacity(u);
    for bit in 0..u{
        if epsilon_bin_val[bit] == Scalar::ZERO{
            u_alpha.push(bit);
        }
    }
    let offset = u_alpha[0];
    let u_alpha_view : Vec<usize> = u_alpha.iter().map(|v| v-offset).collect();
    let alpha = u_alpha_view.len()-1;
    let l = u-offset;
    let i_star = find_mpd_i_bigger_than_threshold(mpd_vec_bin, threshold, a);
    // println!("{:?}", i_star);
    // println!("{:?}", u_alpha_view);
    let mut simulate_proofs : Vec<ZKthresholdi> = Vec::with_capacity(a-1);
    let mut simulate_chal_sum = Scalar::ZERO;

    for i in 0..a{
        if i != i_star{
            let (proof_i, chal_i) = simulate_pi_0(&u_alpha_view, &m_bis_vec[i][offset..], h, rng_proof);
            simulate_proofs.push(proof_i);
            simulate_chal_sum += chal_i;
        }
    }

    // ij_star
    let m_i_star = m_bis_vec[i_star];
    let m_i_star_view : &[RistrettoPoint] = &m_i_star[offset..];
    let z_i_star = z_vec[i_star];
    let z_i_star_view : &[Scalar] = &z_i_star[offset..];

    let mut r_j_star : Vec<Scalar> = vec![Scalar::ZERO; l];
    let mut u_j_star : Vec<Scalar> = vec![Scalar::ZERO; l];
    let mut rr_j_star: Vec<RistrettoPoint> = vec![RistrettoPoint::identity(); l];
    let mut c_j_star: Vec<Scalar> = vec![Scalar::ZERO; l];

    // deduce the last true term
    let mut stop_term = None;

    for index in (0..alpha+1).rev() {
        let ind = u_alpha_view[index];
        if m_i_star_view[ind] == z_i_star_view[ind] * h {
            stop_term = Some(ind);
            break;
        }
    }
    let stop_term = stop_term.expect("No true term in the i star");

    // for i in (stop_term..l){
    //     if d_ij_star_view[i] != w_ij_star_view[i] * h{
    //         // println!("wrong for bit : {}", i);
    //     }
    // }
    
    // println!("First true: {}", stop_term);
    let mut c_current_right = Scalar::ZERO;
    if stop_term == 0{
        // stop in the last relation, prove all big et, simule all u_alpha except 0
        let mut cursor = 1;
        for i in 0..l{
            if cursor <= alpha && i == u_alpha_view[cursor]{
                // simule
                u_j_star[i] = random_scalar(rng_proof);
                let _ = simulate_c_and_rr(i,
                    &mut c_j_star, 
                    &mut rr_j_star, 
                    &m_i_star_view, 
                    &u_j_star, 
                    h,
                    rng_proof
                );
                cursor += 1;
            }
            else{
                r_j_star[i] = random_scalar(rng_proof);
                rr_j_star[i] = r_j_star[i] * h;
            }
        }
    }
    else{
        // stop in relation k, prove all big vee in the left, simulate all terms in the right
        u_j_star[0] = random_scalar(rng_proof);
        let c_0 = simulate_c_and_rr(0, &mut c_j_star, 
            &mut rr_j_star, 
            &m_i_star_view, 
            &u_j_star, 
            h,
            rng_proof
        );
        let mut cursor = 1;
        let mut c_current = c_0;
        for i in 0..stop_term{
            if i == u_alpha_view[cursor]{
                u_j_star[i] = random_scalar(rng_proof);
                let c_i = simulate_c_and_rr(i, &mut c_j_star, 
                    &mut rr_j_star, 
                    &m_i_star_view, 
                    &u_j_star, 
                    h,
                    rng_proof
                );
                c_current += c_i;
                cursor += 1;
            }
            else{
                u_j_star[i] = random_scalar(rng_proof);
                c_j_star[i] = c_current;
                rr_j_star[i] = u_j_star[i] * h - c_j_star[i] * m_i_star_view[i];
            }
        }
        c_current_right = c_current;

        cursor += 1;
        for i in stop_term..l{
            if cursor > alpha || i != u_alpha_view[cursor]{
                r_j_star[i] = random_scalar(rng_proof);
                rr_j_star[i] = r_j_star[i] * h;
            }
            else{
                u_j_star[i] = random_scalar(rng_proof);
                c_j_star[i] = random_scalar(rng_proof);
                rr_j_star[i] = u_j_star[i] * h - c_j_star[i] * m_i_star_view[i];
                cursor += 1;
            }
            
        }
    }
    
    // aggregate rr the same way as verifier
    let mut rr_agg = Vec::with_capacity(a * l);
    let mut y_agg  = Vec::with_capacity(a * l);

    let mut buf = 0;
    for i in 0..a {
        if i == i_star {
            for x in &rr_j_star {
                rr_agg.push(*x);
            }
        } else {
            for x in &simulate_proofs[buf].commitments {
                rr_agg.push(*x);
            }
            buf += 1;
        }

        for d_ij in &m_bis_vec[i][offset..] {
            y_agg.push(*d_ij);
        }
    }

    let chal = chal_list(
        &rr_agg,
        &y_agg,
        &vec![h; a * l]
    );

    // deduce chal_j_star
    let chal_ij_star = chal - simulate_chal_sum;

    // calculate c and u for the proved term for ij_star
    if stop_term == 0{
        let mut c_current = chal_ij_star;
        let mut end_ind = alpha;
        for i in (0..l).rev(){
            if end_ind > 0 && i == u_alpha_view[end_ind]{
                c_current -= c_j_star[i];
                end_ind -= 1;
            }
            else{
                c_j_star[i] = c_current;
                u_j_star[i] = r_j_star[i] + c_j_star[i] * z_i_star_view[i];
            }
        }
    }else{
        let mut c_current = chal_ij_star;
        let mut end_ind = alpha;
        for i in (stop_term+1..l).rev(){
            // println!("i={}", i);
            if i == u_alpha_view[end_ind]{
                c_current -= c_j_star[i];
                end_ind -= 1;
            }
            else{
                // println!("{:?}", c_current == chal_ij_star);
                c_j_star[i] = c_current;
                u_j_star[i] = r_j_star[i] + c_j_star[i] * z_i_star_view[i];
            }
        }
        c_j_star[stop_term] = c_current - c_current_right;
        u_j_star[stop_term] = r_j_star[stop_term] + c_j_star[stop_term] * z_i_star_view[stop_term];
    }
    // for i in 0..l{
    //     assert!(c_j_star[i]!=Scalar::ZERO);
    //     assert!(u_j_star[i]!=Scalar::ZERO);
    // }

    let proof_i_star = ZKthresholdi{commitments: rr_j_star, challenges: c_j_star, responses: u_j_star};
    let mut proofs : Vec<ZKthresholdi> = Vec::with_capacity(a);

    let mut buffer = 0;
    for i in 0..a{
        if i==i_star{
            proofs.push(proof_i_star.clone());
        }
        else{
            proofs.push(simulate_proofs[buffer].clone());
            buffer += 1;
        }
    }
    
    return proofs;

}

pub fn verify_anomaly(
    n: usize,
    m: usize,
    u: usize,
    proofs: &[ZKthresholdi],
    y: &[&[RistrettoPoint]],
    h: RistrettoPoint,
    threshold: Scalar
)->bool{
    let a = n-m+1;
    let epsilon_bin_val = scalar_to_bits(&threshold, u);
    let mut u_alpha : Vec<usize> = Vec::with_capacity(u);
    for bit in 0..u{
        if epsilon_bin_val[bit] == Scalar::ZERO{
            u_alpha.push(bit);
        }
    }
    let offset = u_alpha[0];
    let u_alpha_view : Vec<usize> = u_alpha.iter().map(|v| v-offset).collect();
    let alpha = u_alpha_view.len()-1;
    let l = u-offset;
    // println!("l={}", l);
    // println!("{:?}", possible_ij_set);

    let mut cursor = 0;
    let mut proof_ij : ZKthresholdi;
    let mut y_ij: &[RistrettoPoint];
    let mut res = true;

    let mut chal_aggregated = Scalar::ZERO;

    for i in 0..a{
        proof_ij = proofs[cursor].clone();
        y_ij = y[i].clone();
        let y_ij_view = &y_ij[offset..];

        let rr = &proof_ij.commitments;
        let c = &proof_ij.challenges;
        let u = &proof_ij.responses;

        let mut c_current = c[0];
        let mut buffer = 1;
        for bit in 0..l{
            if buffer <= alpha && bit == u_alpha_view[buffer]{
                c_current += c[bit];
                buffer += 1;
            }
            else{
                let ans = c[bit] == c_current;
                if ans == false{
                    println!("c[bit] == c_current wrong for i={}, bit={}", i, bit);
                }

                res &= ans;
            }
            let ans_res = (rr[bit] == u[bit] * h - c[bit] * y_ij_view[bit]);
            res &= ans_res;
            if ans_res == false{
                println!("rr=h^u/y^c wrong for i={}, bit={}", i, bit);
            }
        }
        let chal_ij = c_current;
        chal_aggregated += chal_ij;
        cursor += 1;
    }

    let mut rr_agg = Vec::with_capacity(a * l);
    let mut y_agg  = Vec::with_capacity(a * l);

    let mut buf = 0;
    for i in 0..a {
        let proof = proofs[buf].clone();
        let rr = proof.commitments;
        for x in &rr {
            rr_agg.push(*x);
        }

        for d_ij in &y[i][offset..] {
            y_agg.push(*d_ij);
        }
        buf += 1;
    }

    let chal = chal_list(&rr_agg.clone(), &y_agg.clone(), &vec![h; a*l]);
    let res_chal = chal == chal_aggregated;
    res &= res_chal;
    // println!("challenge sum verified ? {}", res_chal);
    res
}

pub fn measure_time_comp_anomaly(
    upper: usize,
    n: usize,   // length of time series
    m: usize,   // window size
    u: usize, // number of bits (ℓ)
    iter: usize,
    epsilon: u64
) {
    let a = n - m + 1; // number of MPD entries (indices i ∈ I

    let mut time_proof_threshold  = Duration::ZERO;
    let mut time_verify_threshold = Duration::ZERO;

    for _ in 0..iter {
        let mut rng       = OsRng;
        let mut rng_k     = OsRng;
        let mut rng_proof = OsRng;

        // --- 1) Initialize TS and MPD and threshold -------------------------------
        let ts = random_ecg(&mut rng, n, upper);
        // println!("{:?}", ts);

        let threshold : Scalar = Scalar::from(epsilon);

        // --- 2) Setup ----------------------------------------------------
        let mut set = setup(n, &mut rng);

        let g = set.gen;
        let h = set.h_;

        // --- 3) Commit original time series --------
        let commitment = commit(&mut set, &ts.to_vec(), &mut rng_k);
        
        // --- 4) Commit MPD --------
        let mpd      = compute_mpd_with_window_scalar(&ts, m);
        let mpd_bin: Vec<Vec<Scalar>> = mpd.iter().map(|x| scalar_to_bits(x, u)).collect();
        let (m_vec, m_bis_vec, z_vec) = calculate_mpd_commit(&g, &h, mpd_bin, u, &mut rng_proof);

        let m_bis_vec_refs: Vec<&[RistrettoPoint]> = m_bis_vec.iter().map(|x| x.as_slice()).collect();
        let z_vec_refs: Vec<&[Scalar]> = z_vec.iter().map(|inner| inner.as_slice()).collect();

        // --- 12) Proof threshold time --------------
        let t2 = Instant::now();
        let proofs = prove_comp_anomaly(threshold, mpd, n, m, u, &m_bis_vec_refs, &z_vec_refs, h, &mut rng_proof);
        let duration_proof_threshold = t2.elapsed();
        time_proof_threshold += duration_proof_threshold;
        println! ("Proof Threshold : {:?}", duration_proof_threshold);

        let t3 = Instant::now();
        let res = verify_anomaly(n, m, u, &proofs, &m_bis_vec_refs, h, threshold);
        let duration_verify_threshold = t3.elapsed();
        time_verify_threshold += duration_verify_threshold; 
        println! ("Verify Threshold : {:?}", duration_verify_threshold);

        println!("==== Verify for Threshold : {} ==== ", res);
    }

    println!("==== Timing over {} iterations ====", iter);
    println!("  proof (Threshold):   {:?}", time_proof_threshold/(iter as u32));
    println!("  verify (Threshold):  {:?}", time_verify_threshold/(iter as u32));
}
