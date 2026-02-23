use crate::comp::{simulate_c_and_rr};
use crate::usefulstructs::*;
use crate::usefulfuncs::{scalar_to_u64, random_ecg, random_ristretto_point, random_scalar, chal_single_proof_square, chal_distance, random_vec_scalar, lincomb_pow2, two_pow, scalar_to_bits, compute_mpd_with_window_scalar, chal_list};
use curve25519_dalek::{ scalar::Scalar, RistrettoPoint, traits::Identity};
use rand_core::{ OsRng, CryptoRng, RngCore, CryptoRngCore };   
use std::time::{ Instant, Duration }; 

use crate::square::*;        
use crate::distance::*;  
use crate::mpd_bin::*;  
use crate::mpd_exist::*;
use crate::mpd_min::*;
use crate::threshold::*;
use crate::comp::*;
use crate::commit::*;

pub fn proofs_size(n: usize, m: usize) -> usize{
    let half_m = m/2;
    let a = n - m + 1;
    let mut count = 0;
    let mut left_end = 0;
    let mut right_start = 0;

    for i in 0..a{
        let left_end = i.saturating_sub(half_m);
        right_start = (i + half_m + 1).min(a);
        for j in (0..left_end).chain((right_start..a)){
            count += 1;
        }
    }
    count
}

// find the i where for all j, d_ij > epsilon
pub fn find_i_star(
    d_ij: Vec<Scalar>,
    threshold: Scalar,
    a: usize,
    m: usize
) -> usize {
    
    let thr = scalar_to_u64(threshold);
    let half_m = m / 2;
    let mut left_end = 0;
    let mut right_start = 0;
    let mut i_star = true;

    for i in 0..a {
        let left_end = i.saturating_sub(half_m);
        right_start = (i + half_m + 1).min(a);
        i_star = true;
        for j in (0..left_end).chain((right_start..a)){
            let value = scalar_to_u64(d_ij[i * a + j]);
            if value <= thr {
                i_star = false;
                break;
            }
        }
        if i_star{
            return i;
        }
    }

    println!("WARNING: No i where all distances greater than the threshold!");
    0
}


pub fn simulate_pi_0<T: CryptoRngCore>(
    u_alpha_view: &[usize],
    d_ij_view: &[RistrettoPoint],
    h: RistrettoPoint,
    rng_proof: &mut T,
    challenge_pi: Scalar
)->ZKthresholdi{
    let l = d_ij_view.len();
    // println!("simulate proof l={}", l);

    let mut c : Vec<Scalar> = vec![Scalar::ZERO; l]; // challenges
    let mut rr : Vec<RistrettoPoint> = Vec::with_capacity(l); // R
    // compute the responses
    let u : Vec<Scalar> = (0..l).map(|_| random_scalar(rng_proof)).collect(); // responses

    let alpha = u_alpha_view.len()-1;
    let mut begin: usize;
    let mut end: usize;
    
    c[0] = random_scalar(rng_proof);
    let mut cursor = alpha;
    let mut c_current = challenge_pi;
    for i in (0..l).rev(){
        if cursor >= 1 && i == u_alpha_view[cursor]{
            c[i] = random_scalar(rng_proof);
            c_current -= c[i];
            cursor -= 1;
        }
        else{
            c[i] = c_current;
        }
    }
    // sanity check and compute the commitements R
    for i in 0..l{
        assert!(c[i]!=Scalar::ZERO);
        rr.push(u[i]*h - c[i]*d_ij_view[i]);
    }

    ZKthresholdi{commitments: rr, challenges: c, responses: u}
}

pub fn prove_comp_anomaly<T: CryptoRngCore>(
    threshold: Scalar,
    d_private_vec: Vec<Scalar>,
    n: usize,
    m: usize,   
    u: usize,
    d_vec: &[&[RistrettoPoint]], // d_vec/g
    w_vec:  &[&[Scalar]],
    h: RistrettoPoint,
    rng_proof: &mut T
)->Vec<ZKthresholdi>{
    println!("Length of d_vec: {}", d_vec.len());
    let a = n-m+1;
    let epsilon_bin_val = scalar_to_bits(&Scalar::from(threshold), u);
    let mut u_alpha : Vec<usize> = Vec::with_capacity(u);
    let mut simulate_chal_sum = Scalar::ZERO;
    let half_m = m/2;
    for bit in 0..u{
        if epsilon_bin_val[bit] == Scalar::ZERO{
            u_alpha.push(bit);
        }
    }
    let offset = u_alpha[0];
    let u_alpha_view : Vec<usize> = u_alpha.iter().map(|v| v-offset).collect();
    let alpha = u_alpha_view.len()-1;
    let l = u-offset;
    let i_star = find_i_star(d_private_vec, threshold, a, m);
    let proof_size = proofs_size(n, m);

    println!("Proof size :{:?}", proof_size);
    println!("i star: {:?}", i_star);
    println!("u alpha view: {:?}", u_alpha_view);
    println!("bit length : {}", l);

    let mut simulate_proofs : Vec<ZKthresholdi> = Vec::with_capacity(proof_size);

    for i in 0..a{
        if i != i_star{
            let left_end = i.saturating_sub(half_m);
            let right_start = (i + half_m + 1).min(a);
            let c_i = random_scalar(rng_proof);
            for j in (0..left_end).chain((right_start..a)){
                let proof_ij = simulate_pi_0(&u_alpha_view, &d_vec[i*a+j][offset..], h, rng_proof, c_i);
                simulate_proofs.push(proof_ij);
            }
            simulate_chal_sum += c_i;
        }
    }

    // boucle j for i_star
    let left_end_i_star = i_star.saturating_sub(half_m);
    let right_start_i_star = (i_star + half_m + 1).min(a);
    // aggregate rr the same way as verifier
    let mut rr_agg = Vec::with_capacity(proof_size * l);
    let mut y_agg  = Vec::with_capacity(proof_size * l);
    let mut rr_i_star = Vec::with_capacity(left_end_i_star + a - right_start_i_star);
    let mut c_i_star = Vec::with_capacity(left_end_i_star + a - right_start_i_star);
    let mut r_i_star = Vec::with_capacity(left_end_i_star + a - right_start_i_star);
    let mut u_i_star = Vec::with_capacity(left_end_i_star + a - right_start_i_star);
    let mut stop_i_star = Vec::with_capacity(left_end_i_star + a - right_start_i_star);
    let num_j_i_star = (left_end_i_star) + (a - right_start_i_star);
    let mut c_right_i_star = Vec::with_capacity(left_end_i_star + a - right_start_i_star);

    println!("Generating proofs for i_star...");
    for j_star in (0..left_end_i_star).chain((right_start_i_star..a)){
        let d_ij_star = d_vec[i_star*a+j_star];
        let d_ij_star_view : &[RistrettoPoint] = &d_ij_star[offset..];
        let w_ij_star = w_vec[i_star*a+j_star];
        let w_ij_star_view : &[Scalar] = &w_ij_star[offset..];

        let mut r_j_star: Vec<Scalar> = vec![Scalar::ZERO; l];
        let mut u_j_star: Vec<Scalar> = vec![Scalar::ZERO; l];
        let mut rr_j_star: Vec<RistrettoPoint> = vec![RistrettoPoint::identity(); l];
        let mut c_j_star: Vec<Scalar> = vec![Scalar::ZERO; l];

        // deduce the last true term
        let mut stop_term = None;

        for index in (0..alpha+1).rev() {
            let ind = u_alpha_view[index];
            if d_ij_star_view[ind] == w_ij_star_view[ind] * h {
                stop_term = Some(ind);
                break;
            }
        }
        let stop_term = stop_term.expect("No true term in the ij star");
        // println!("Stop term : {}", stop_term);

        // for x in (stop_term..l){
        //     if d_ij_star_view[x] != w_ij_star_view[x] * h{
        //         println!("wrong for bit : {}", x);
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
                        &d_ij_star_view, 
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
            // stop in relation k, prove all big et in the left, simulate all terms in the right
            u_j_star[0] = random_scalar(rng_proof);
            let c_0 = simulate_c_and_rr(0, &mut c_j_star, 
                &mut rr_j_star, 
                &d_ij_star_view, 
                &u_j_star, 
                h,
                rng_proof
            );
            let mut cursor = 1;
            let mut c_current = c_0;
            for i in 1..stop_term{
                if i == u_alpha_view[cursor]{
                    u_j_star[i] = random_scalar(rng_proof);
                    let c_i = simulate_c_and_rr(i, &mut c_j_star, 
                        &mut rr_j_star, 
                        &d_ij_star_view, 
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
                    rr_j_star[i] = u_j_star[i] * h - c_j_star[i] * d_ij_star_view[i];
                }
            }
            c_current_right = c_current;
            // println!("j_star = {}, cursor = {}", j_star, cursor);
            cursor += 1;
            for i in stop_term..l{
                if cursor > alpha || i != u_alpha_view[cursor]{
                    r_j_star[i] = random_scalar(rng_proof);
                    rr_j_star[i] = r_j_star[i] * h;
                }
                else{
                    u_j_star[i] = random_scalar(rng_proof);
                    c_j_star[i] = random_scalar(rng_proof);
                    rr_j_star[i] = u_j_star[i] * h - c_j_star[i] * d_ij_star_view[i];
                    cursor += 1;
                }
            }
        }
        // push rr
        rr_i_star.push(rr_j_star);
        c_i_star.push(c_j_star);
        r_i_star.push(r_j_star);
        u_i_star.push(u_j_star);
        stop_i_star.push(stop_term);
        c_right_i_star.push(c_current_right);
    }

    // gather public elements to call hash function
    let mut buf = 0;
    let mut j_star_buf = 0; 

    for i in 0..a {
        let left_end = i.saturating_sub(half_m);
        let right_start = (i + half_m + 1).min(a);

        for j in (0..left_end).chain(right_start..a) {
            
            // 1. Fill rr_agg
            if i == i_star {
                for point in &rr_i_star[j_star_buf] {
                    rr_agg.push(*point);
                }
                j_star_buf += 1;
            } else {
                for point in &simulate_proofs[buf].commitments {
                    rr_agg.push(*point);
                }
                buf += 1;
            }

            // 2. Fill y_agg (keeping the order perfectly aligned with rr_agg)
            for d_ij in &d_vec[i * a + j][offset..] {
                y_agg.push(*d_ij);
            }
        }
    }

    let chal = chal_list(
        &rr_agg,
        &y_agg,
        &vec![h; proof_size * l]
    );

    // deduce chal_i_star
    let k = Scalar::from(num_j_i_star as u64);
    let chal_i_star = chal - simulate_chal_sum;

    // calculate c and u for the proved term for i_star
    let mut buf = 0;
    let mut proofs_i_star = Vec::with_capacity(c_i_star.len());
    for j_star in (0..left_end_i_star).chain((right_start_i_star..a)){
        let w_ij_star = w_vec[i_star*a+j_star];
        let w_ij_star_view : &[Scalar] = &w_ij_star[offset..];
        let stop_term = stop_i_star[buf];
        let c_j_star = &mut c_i_star[buf];
        let u_j_star = &mut u_i_star[buf];
        let r_j_star = &mut r_i_star[buf];
        let rr_j_star_ref = &mut rr_i_star[buf];
        let c_current_right = c_right_i_star[buf];

        if stop_term == 0{
            let mut c_current = chal_i_star;
            let mut end_ind = alpha;
            for i in (0..l).rev(){
                if end_ind > 0 && i == u_alpha_view[end_ind]{
                    c_current -= c_j_star[i];
                    end_ind -= 1;
                }
                else{
                    c_j_star[i] = c_current;
                    u_j_star[i] = r_j_star[i] + c_j_star[i] * w_ij_star_view[i];
                }
            }
        } else { // stop_term > 0
            let mut c_current = chal_i_star;
            let mut end_ind = alpha;

            // 1. Fill the Right side (stop_term + 1 to l)
            for i in (stop_term + 1..l).rev() {
                if i == u_alpha_view[end_ind] {
                    c_current -= c_j_star[i];
                    end_ind -= 1;
                } else {
                    c_j_star[i] = c_current;
                    // Response was already r_j_star + c_j_star * w in first pass? 
                    // Better to re-set it to be safe:
                    u_j_star[i] = r_j_star[i] + c_j_star[i] * w_ij_star_view[i];
                }
            }

            // 2. Set the Bridge (stop_term)
            c_j_star[stop_term] = c_current - c_current_right;
            u_j_star[stop_term] = r_j_star[stop_term] + c_j_star[stop_term] * w_ij_star_view[stop_term];

        }
        for i in 0..l{
            assert!(c_j_star[i]!=Scalar::ZERO);
            assert!(u_j_star[i]!=Scalar::ZERO);
        }
        let proof_j_star = ZKthresholdi {
            commitments: rr_j_star_ref.to_vec(), 
            challenges: c_j_star.to_vec(), 
            responses: u_j_star.to_vec(),
        };
        proofs_i_star.push(proof_j_star);
        buf += 1 ;
    }

    let mut proofs : Vec<ZKthresholdi> = Vec::with_capacity(proof_size);
    
    let mut buffer = 0;
    for i in 0..a{
        if i == i_star{
            for proof in &proofs_i_star{
                proofs.push(proof.clone());
            }
        }
        else{
            let left_end = i.saturating_sub(half_m);
            let right_start = (i + half_m + 1).min(a);
            for j in (0..left_end).chain((right_start..a)){
                proofs.push(simulate_proofs[buffer].clone());
                buffer += 1;
            }
        }
    }
    println!("Simulate_proofs length : {}", simulate_proofs.len());
    println!("Pushed proof count: {}", proofs.len());
    
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
    let proof_size = proofs_size(n, m);

    let mut cursor = 0;
    let mut proof_ij : ZKthresholdi;
    let mut y_ij: &[RistrettoPoint];
    let mut res = true;

    let mut chal_aggregated = Scalar::ZERO;
    let mut rr_agg = Vec::with_capacity(proof_size * l);
    let mut y_agg  = Vec::with_capacity(proof_size * l);
    let half_m = m / 2;

    for i in (0..a){
        let left_end = i.saturating_sub(half_m);
        let right_start = (i + half_m + 1).min(a);
        let mut challenge_i = Scalar::ZERO;
        for j in (0..left_end).chain((right_start..a)){
            proof_ij = proofs[cursor].clone();
            y_ij = y[i*a+j].clone();
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
                    res &= c[bit] == c_current;
                    // if c[bit] != c_current{
                    //     println!("c[bit] == c_current wrong for i={}, j={}, bit={}", i, j, bit);
                        
                    // }
                }
                res &= (rr[bit] == u[bit] * h - c[bit] * y_ij_view[bit]);
                rr_agg.push(rr[bit]);
                y_agg.push(y_ij_view[bit]);
                // if rr[bit] != u[bit] * h - c[bit] * y_ij_view[bit]{
                //     println!("rr=h^u/y^c wrong for i={}, j={}, bit={}", i, j, bit);
                // }
            }
            
            let chal_ij = c_current;
            if challenge_i == Scalar::ZERO{
                challenge_i = chal_ij;
            }
            else{
                res &= chal_ij == challenge_i;
                if res == false{
                    println!("challenge not equal for the same i");
                }
            }
            cursor += 1;
        }
        chal_aggregated += challenge_i;
    }
    println!("rr_agg length : {}", rr_agg.len());
    println!("y_agg length : {}", y_agg.len());
    println!("proof size : {}", proof_size);
    let chal = chal_list(&rr_agg.clone(), &y_agg.clone(), &vec![h; proof_size*l]);
    res &= chal == chal_aggregated;
    if chal != chal_aggregated{
        println!("Challenge sum verification failed");
    }
    println!("challenge sum verified ? {}", chal==chal_aggregated);
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

        // --- 4) Commit square --------
        let (c_diff, c_tilde, x_diff, k_diff, k_tilde) = calculate_inner_diff_commit(&commitment, &set, &mut rng);

        // --- 7) Commit Distance -----
        let (c_vec, c_bis_vec, w, d_private_bin_vec, d_private_vec) = calculate_dist_commit(&mut rng_proof, n, m, u, g, h, &x_diff, &k_diff, &k_tilde);
        
        let c_vec_refs: Vec<&[RistrettoPoint]> = c_vec.iter().map(|inner| inner.as_slice()).collect();
        let c_bis_vec_refs: Vec<&[RistrettoPoint]> = c_bis_vec.iter().map(|inner| inner.as_slice()).collect();
        let w_refs : Vec<&[Scalar]> = w.iter().map(|inner| inner.as_slice()).collect();
        let d_private_bin_refs : Vec<&[Scalar]> = d_private_bin_vec.iter().map(|inner| inner.as_slice()).collect();

        // --- 12) Proof threshold time --------------

        let t2 = Instant::now();
        let proofs = prove_comp_anomaly(threshold, d_private_vec, n, m, u, &c_bis_vec_refs, &w_refs, h, &mut rng_proof);
        let duration_proof_threshold = t2.elapsed();
        time_proof_threshold += duration_proof_threshold;
        println! ("Proof Threshold : {:?}", duration_proof_threshold);

        let t3 = Instant::now();
        let res = verify_anomaly(n, m, u, &proofs, &c_bis_vec_refs, h, threshold);
        let duration_verify_threshold = t3.elapsed();
        time_verify_threshold += duration_verify_threshold; 
        println! ("Verify Threshold : {:?}", duration_verify_threshold);

        println!("==== Verify for Threshold : {} ==== ", res);
    }

    println!("==== Timing over {} iterations ====", iter);
    println!("  proof (Threshold):   {:?}", time_proof_threshold/(iter as u32));
    println!("  verify (Threshold):  {:?}", time_verify_threshold/(iter as u32));
}

#[cfg(test)]
mod tests{
    use super::*;

    #[test]
    fn test_possible_ij_set(){
        let n = 10;
        let m = 4;
        let half_m = m/2;
        let ground_truth = vec![(0,3),(0,4),(0,5),(0,6),(1,4),(1,5),(1,6),(2,5),(2,6),(3,6)];
        assert_eq!(possible_ij_set(n,m), ground_truth);
    }

    #[test]
    fn test_find_ij_smaller_than_threshold(){
        let d_ij = vec![Scalar::from(0u64), Scalar::from(45u64), Scalar::from(5u64), Scalar::from(7u64), Scalar::from(9u64), Scalar::from(0u64), Scalar::from(3u64), Scalar::from(5u64), Scalar::from(7u64), Scalar::from(0u64)];
        let possible_ij_set = vec![(0,3),(0,4),(1,4)];
        let a = 5;
        let threshold = Scalar::from(3u64);
        let ground_truth = (1,4);
        assert_eq!(find_ij_smaller_than_threshold(d_ij,possible_ij_set, threshold, a), ground_truth);
    }

    #[test]
    fn test_find_ij_smaller_than_threshold_wrong(){
        let d_ij = vec![Scalar::from(0u64), Scalar::from(45u64), Scalar::from(5u64), Scalar::from(7u64), Scalar::from(9u64), Scalar::from(0u64), Scalar::from(3u64), Scalar::from(5u64), Scalar::from(7u64), Scalar::from(0u64)];
        let possible_ij_set = vec![(0,3),(0,4),(1,4)];
        let a = 5;
        let threshold = Scalar::from(0u64);
        let ground_truth = (0,3);
        assert_eq!(find_ij_smaller_than_threshold(d_ij,possible_ij_set, threshold, a), ground_truth);
    }
}

