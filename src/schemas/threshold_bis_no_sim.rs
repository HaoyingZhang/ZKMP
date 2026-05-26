use curve25519_dalek::{ scalar::Scalar, RistrettoPoint, traits::Identity};
use crate::comp_bis::{simulate_pi_0, scalar_to_u64};
use rand_core::{ CryptoRng, RngCore, CryptoRngCore, OsRng };  
use crate::comp_bis::*;
use crate::usefulstructs::*;
use crate::usefulfuncs::{random_ecg, random_ristretto_point, random_scalar, chal_single_proof_square, chal_distance, random_vec_scalar, lincomb_pow2, two_pow, scalar_to_bits, compute_mpd_with_window_scalar, chal_list};
use std::time::{ Instant, Duration }; 
use std::io::Write;

use crate::square::*;        
use crate::distance::*;  
use crate::mpd_bin::*;  
use crate::mpd_exist::*;
use crate::mpd_min::*;
use crate::threshold::*;
use crate::comp::*;
use crate::commit::*;

// all the distances sup than delta

pub fn prove_comp_no_sim<T: CryptoRngCore>(
    threshold: Scalar,
    n: usize,
    m: usize,
    u: usize,
    d_ij_bis_vec: &[&[RistrettoPoint]],
    w_ij_vec:  &[&[Scalar]],
    h: RistrettoPoint,
    rng_proof: &mut T
)->Vec<ZKthresholdi>{
    let a = n-m+1;
    let ij_set = possible_ij_set(n, m);
    let ij_set_length = ij_set.len();
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

    // ++++ prove i,j ++++
    let mut proofs : Vec<ZKthresholdi> = Vec::with_capacity(ij_set_length);
    let mut rr_aggregated : Vec<RistrettoPoint> = Vec::with_capacity(ij_set_length);
    let mut c_aggregated : Vec<Vec<Scalar>> = Vec::with_capacity(ij_set_length);
    let mut u_aggregated : Vec<Vec<Scalar>> = Vec::with_capacity(ij_set_length);
    let mut r_aggregated : Vec<Vec<Scalar>> = Vec::with_capacity(ij_set_length);
    let mut y_aggregated : Vec<RistrettoPoint> = Vec::with_capacity(ij_set_length);
    let mut stop_terms: Vec<usize> = Vec::with_capacity(ij_set_length);
    let mut c_currents: Vec<Scalar> = Vec::with_capacity(ij_set_length);
    for (i,j) in &ij_set{
        let (rr_ij, c_ij, u_ij, r_ij, stop_term, c_current) = prove_threshold_ij(d_ij_bis_vec, w_ij_vec, *i, *j, h, a, offset, l, &u_alpha_view, rng_proof);
        let y_ij : &[RistrettoPoint] = &d_ij_bis_vec[i*a+j][offset..];
        for rr in rr_ij{
            rr_aggregated.push(rr);
        }
        for y in y_ij{
            y_aggregated.push(*y);
        }
        
        c_aggregated.push(c_ij);
        u_aggregated.push(u_ij);
        r_aggregated.push(r_ij);
        stop_terms.push(stop_term);
        c_currents.push(c_current);
    }


    let chal = chal_list(
        &rr_aggregated,
        &y_aggregated,
        &vec![h; ij_set_length*l]
    );

    // for i in 0..l{
    //     assert!(c_j_star[i]!=Scalar::ZERO);
    //     assert!(u_j_star[i]!=Scalar::ZERO);
    // }
    let mut ind = 0;
    for (i,j) in &ij_set{
        let proof = complete_prove_ij(chal, &w_ij_vec[i*a+j][offset..], (&rr_aggregated[ind*l..ind*l+l]).to_vec(), c_aggregated[ind].clone(), u_aggregated[ind].clone(), r_aggregated[ind].clone(), stop_terms[ind], c_currents[ind], l, alpha, &u_alpha_view);
        proofs.push(proof.clone());
        ind += 1;
    }
    
    return proofs;

}

pub fn prove_threshold_ij<T: CryptoRngCore>(
    m_bis_vec : &[&[RistrettoPoint]],
    z_vec: &[&[Scalar]],
    i_star: usize,
    j_star: usize,
    h: RistrettoPoint,
    a: usize,
    offset: usize,
    l: usize,
    u_alpha_view: &[usize],
    rng_proof: &mut T
)->(Vec<RistrettoPoint>, Vec<Scalar>, Vec<Scalar>, Vec<Scalar>, usize, Scalar){
    let alpha = u_alpha_view.len()-1;
    // ij_star
    let m_i_star = m_bis_vec[i_star*a+j_star];
    let m_i_star_view : &[RistrettoPoint] = &m_i_star[offset..];
    let z_i_star = z_vec[i_star*a+j_star];
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
    (rr_j_star, c_j_star, u_j_star, r_j_star, stop_term, c_current_right)
}

pub fn complete_prove_ij(
    chal_ij_star: Scalar,
    w_i_star_view: &[Scalar],
    mut rr_j_star: Vec<RistrettoPoint>,
    mut c_j_star: Vec<Scalar>,
    mut u_j_star: Vec<Scalar>,
    mut r_j_star: Vec<Scalar>,
    stop_term: usize,
    c_current_right : Scalar,
    l: usize,
    alpha: usize,
    u_alpha_view: &[usize]
)->ZKthresholdi{
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
                u_j_star[i] = r_j_star[i] + c_j_star[i] * w_i_star_view[i];
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
                u_j_star[i] = r_j_star[i] + c_j_star[i] * w_i_star_view[i];
            }
        }
        c_j_star[stop_term] = c_current - c_current_right;
        u_j_star[stop_term] = r_j_star[stop_term] + c_j_star[stop_term] * w_i_star_view[stop_term];
    }
    
    let proof = ZKthresholdi{commitments: rr_j_star, challenges: c_j_star, responses: u_j_star};
    proof
}


pub fn verify_no_similarity(
    n: usize,
    m: usize,
    u: usize,
    proofs: &[ZKthresholdi],
    y: &[&[RistrettoPoint]],
    h: RistrettoPoint,
    threshold: Scalar
)->bool{
    let a = n-m+1;
    let ij_set = possible_ij_set(n, m);
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

    for (i,j) in &ij_set{
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
        if chal_aggregated == Scalar::ZERO{
            chal_aggregated = chal_ij;
        }
        else{
            let chal_ij_verify = chal_aggregated == chal_ij;
            if chal_ij_verify == false{
                println!("Challenge verify not equal for i = {}, j={}", i, j);
                res &= chal_ij_verify;
            }
        }
        cursor += 1;
    }

    let mut rr_agg = Vec::with_capacity(a * l);
    let mut y_agg  = Vec::with_capacity(a * l);

    let mut buf = 0;
    for (i, j) in &ij_set {
        let proof = proofs[buf].clone();
        let rr = proof.commitments;
        for x in &rr {
            rr_agg.push(*x);
        }

        for d_ij in &y[i*a+j][offset..] {
            y_agg.push(*d_ij);
        }
        buf += 1;
    }

    let chal = chal_list(&rr_agg.clone(), &y_agg.clone(), &vec![h; ij_set.len()*l]);
    let res_chal = chal == chal_aggregated;
    res &= res_chal;
    println!("challenge sum verified ? {}", res_chal);
    res
}

pub fn measure_time_comp_no_similarity(
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

    for _i in 0..iter {
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
        
        let (_, _, x_diff, k_diff, k_tilde) = calculate_inner_diff_commit(&commitment, &set, &mut rng_proof);
        
        let _t1 = Instant::now();
        let (_, d_vec_bis, w_vec, _, _) = calculate_dist_commit(&mut rng_proof, n, m, u, g, h, &x_diff, &k_diff, &k_tilde);


        let d_bis_vec_refs: Vec<&[RistrettoPoint]> =d_vec_bis.iter().map(|x| x.as_slice()).collect();
        let w_vec_refs: Vec<&[Scalar]> = w_vec.iter().map(|inner| inner.as_slice()).collect();

        // --- 12) Proof threshold time --------------
        let t2 = Instant::now();
        let proofs = prove_comp_no_sim(threshold, n, m, u, &d_bis_vec_refs, &w_vec_refs, h, &mut rng_proof);
        if _i == 0 {
            std::fs::create_dir_all("proofs_script").unwrap();
            let mut file = std::fs::File::create("proofs_script/proofs_comp_non_sim.bin").expect("failed to create proofs file");
            for p in &proofs {
                for c in &p.commitments { file.write_all(c.compress().as_bytes()).unwrap(); }
                for c in &p.challenges  { file.write_all(c.as_bytes()).unwrap(); }
                for r in &p.responses   { file.write_all(r.as_bytes()).unwrap(); }
            }
            drop(file);
            let size = std::fs::metadata("proofs_script/proofs_comp_non_sim.bin").unwrap().len();
            println!("proofs_script/proofs_comp_non_sim.bin size: {} bytes ({:.2} KB)", size, size as f64 / 1024.0);
        }

        let duration_proof_threshold = t2.elapsed();
        time_proof_threshold += duration_proof_threshold;
        println! ("Proof Threshold : {:?}", duration_proof_threshold);

        let t3 = Instant::now();
        let res = verify_no_similarity(n, m, u, &proofs, &d_bis_vec_refs, h, threshold);
        let duration_verify_threshold = t3.elapsed();
        time_verify_threshold += duration_verify_threshold; 
        println! ("Verify Threshold : {:?}", duration_verify_threshold);

        println!("==== Verify for Threshold : {} ==== ", res);
    }

    println!("==== Timing over {} iterations ====", iter);
    println!("  proof (Threshold):   {:?}", time_proof_threshold/(iter as u32));
    println!("  verify (Threshold):  {:?}", time_verify_threshold/(iter as u32));
}
