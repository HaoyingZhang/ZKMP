use curve25519_dalek::{ scalar::Scalar, RistrettoPoint, traits::Identity};
use crate::comp::{simulate_c_and_rr};
use rand_core::{ CryptoRng, RngCore, CryptoRngCore };  
use crate::usefulstructs::*;
use crate::usefulfuncs::{random_ecg, random_ristretto_point, random_scalar, chal_single_proof_square, chal_distance, random_vec_scalar, lincomb_pow2, two_pow, scalar_to_bits, compute_mpd_with_window_scalar, chal_list};

pub fn possible_ij_set(n: usize, m: usize) -> Vec<(usize, usize)> {
    let a = n - m + 1;       
    let half_m = m / 2;
    let mut set: Vec<(usize, usize)> = Vec::new();

    for i in 0..a {
        let right_start = (i + half_m + 1).min(a);

        for j in right_start..a {
            set.push((i, j));
        }
    }
    set
}

// we can use the distance value to find ij
pub fn find_ij_smaller_than_threshold(d_ij: Vec<Scalar>, possible_ij_set: Vec<(usize, usize)>, threshold: Scalar, a: usize)->(usize, usize){
    let mut found : bool = false;
    let mut res : (usize, usize) = (0,0);
    for (i,j) in &possible_ij_set{
        if d_ij[i*a+j].to_bytes()<threshold.to_bytes(){
            found = true;
            res = (*i,*j);
            break;
        }
    }
    if found == false{
        println!("Attention! The proof will be wrong since no distance is smaller than the threshold!");
        res = possible_ij_set[0];
    }
    res
}

pub fn simulate_pi_0<T: CryptoRngCore>(
    u_alpha_view: &[usize],
    d_ij_view: &[RistrettoPoint],
    h: RistrettoPoint,
    rng_proof: &mut T
)->(ZKthresholdi,Scalar){
    let l = d_ij_view.len();

    let mut c : Vec<Scalar> = vec![Scalar::ZERO; l]; // challenges
    let mut rr : Vec<RistrettoPoint> = Vec::with_capacity(l); // R
    // compute the responses
    let u : Vec<Scalar> = (0..l).map(|_| random_scalar(rng_proof)).collect(); // responses

    let alpha = u_alpha_view.len()-1;
    let mut begin: usize;
    let mut end: usize;
    
    c[0] = random_scalar(rng_proof);
    let mut cursor = 1;
    let mut c_current = c[0];
    for i in 0..l{
        if cursor <= alpha && i == u_alpha_view[cursor]{
            c[i] = random_scalar(rng_proof);
            c_current += c[i];
            cursor += 1;
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
    let challenge_pi = c_current;

    (ZKthresholdi{commitments: rr, challenges: c, responses: u}, challenge_pi)
}

pub fn prove_comp_similarity<T: CryptoRngCore>(
    threshold: Scalar,
    d_private_vec: Vec<Scalar>,
    n: usize,
    m: usize,
    u: usize,
    d_vec: &[&[RistrettoPoint]],
    w_vec:  &[&[Scalar]],
    h: RistrettoPoint,
    rng_proof: &mut T
)->Vec<ZKthresholdi>{
    let a = n-m+1;
    let epsilon_bin_val = scalar_to_bits(&Scalar::from(threshold), u);
    let mut u_alpha : Vec<usize> = Vec::with_capacity(u);
    for bit in 0..u{
        if epsilon_bin_val[bit] == Scalar::ONE{
            u_alpha.push(bit);
        }
    }
    let offset = u_alpha[0];
    let u_alpha_view : Vec<usize> = u_alpha.iter().map(|v| v-offset).collect();
    let alpha = u_alpha_view.len()-1;
    let l = u-offset;
    let possible_ij_set = possible_ij_set(n, m);
    let (i_star, j_star) = find_ij_smaller_than_threshold(d_private_vec, possible_ij_set.clone(), threshold, a);
    // println!("{:?}", (i_star, j_star));
    // println!("{:?}", u_alpha_view);
    let possible_ij_set_length = possible_ij_set.len();
    let mut simulate_proofs : Vec<ZKthresholdi> = Vec::with_capacity(possible_ij_set_length-1);
    let mut simulate_chal_sum = Scalar::ZERO;

    for (i,j) in &possible_ij_set{
        if (i,j) != (&i_star, &j_star){
            let (proof_ij, chal_ij) = simulate_pi_0(&u_alpha_view, &d_vec[i*a+j][offset..], h, rng_proof);
            simulate_proofs.push(proof_ij);
            simulate_chal_sum += chal_ij;
        }
    }

    // ij_star
    let d_ij_star = d_vec[i_star*a+j_star];
    let d_ij_star_view : &[RistrettoPoint] = &d_ij_star[offset..];
    let w_ij_star = w_vec[i_star*a+j_star];
    let w_ij_star_view : &[Scalar] = &w_ij_star[offset..];

    let mut r_j_star : Vec<Scalar> = vec![Scalar::ZERO; l];
    let mut u_j_star : Vec<Scalar> = vec![Scalar::ZERO; l];
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

    for i in (stop_term..l){
        if d_ij_star_view[i] != w_ij_star_view[i] * h{
            // println!("wrong for bit : {}", i);
        }
    }
    
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
        // stop in relation k, prove all big vee in the left, simulate all terms in the right
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
        for i in 0..stop_term{
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

        for i in stop_term..l{
            r_j_star[i] = random_scalar(rng_proof);
            rr_j_star[i] = r_j_star[i] * h;
        }
    }
    
    // aggregate rr the same way as verifier
    let mut rr_agg = Vec::with_capacity(possible_ij_set_length * l);
    let mut y_agg  = Vec::with_capacity(possible_ij_set_length * l);

    let mut buf = 0;
    for (i, j) in &possible_ij_set {
        if (i, j) == (&i_star, &j_star) {
            for x in &rr_j_star {
                rr_agg.push(*x);
            }
        } else {
            for x in &simulate_proofs[buf].commitments {
                rr_agg.push(*x);
            }
            buf += 1;
        }

        for d_ij in &d_vec[i*a + j][offset..] {
            y_agg.push(*d_ij);
        }
    }

    let chal = chal_list(
        &rr_agg,
        &y_agg,
        &vec![h; possible_ij_set_length * l]
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
                u_j_star[i] = r_j_star[i] + c_j_star[i] * w_ij_star_view[i];
            }
        }
    }else{
        let mut c_current = chal_ij_star;
        let mut end_ind = alpha;
        for i in (stop_term+1..l).rev(){
            // println!("i={}", i);
            if i == u_alpha_view[end_ind]{
                c_j_star[i] = random_scalar(rng_proof);
                u_j_star[i] = r_j_star[i] + c_j_star[i] * w_ij_star_view[i];
                c_current -= c_j_star[i];
                end_ind -= 1;
            }
            else{
                // println!("{:?}", c_current == chal_ij_star);
                c_j_star[i] = c_current;
                u_j_star[i] = r_j_star[i] + c_j_star[i] * w_ij_star_view[i];
            }
        }
        c_j_star[stop_term] = c_current - c_current_right;
        u_j_star[stop_term] = r_j_star[stop_term] + c_j_star[stop_term] * w_ij_star_view[stop_term];
    }
    // for i in 0..l{
    //     assert!(c_j_star[i]!=Scalar::ZERO);
    //     assert!(u_j_star[i]!=Scalar::ZERO);
    // }

    let proof_j_star = ZKthresholdi{commitments: rr_j_star, challenges: c_j_star, responses: u_j_star};
    let mut proofs : Vec<ZKthresholdi> = Vec::with_capacity(possible_ij_set_length);

    let mut buffer = 0;
    for (i,j) in &possible_ij_set{
        if (i,j) == (&i_star, &j_star){
            proofs.push(proof_j_star.clone());
        }
        else{
            proofs.push(simulate_proofs[buffer].clone());
            buffer += 1;
        }
    }
    
    return proofs;

}

pub fn verify_similarity(
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
        if epsilon_bin_val[bit] == Scalar::ONE{
            u_alpha.push(bit);
        }
    }
    let offset = u_alpha[0];
    let u_alpha_view : Vec<usize> = u_alpha.iter().map(|v| v-offset).collect();
    let alpha = u_alpha_view.len()-1;
    let l = u-offset;
    // println!("l={}", l);
    let possible_ij_set = possible_ij_set(n, m);
    // println!("{:?}", possible_ij_set);
    let possible_ij_set_length = possible_ij_set.len();

    let mut cursor = 0;
    let mut proof_ij : ZKthresholdi;
    let mut y_ij: &[RistrettoPoint];
    let mut res = true;

    let mut chal_aggregated = Scalar::ZERO;

    for (i,j) in &possible_ij_set{
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
                if c[bit] != c_current{
                    println!("c[bit] == c_current wrong for i={}, j={}, bit={}", i, j, bit);
                    
                }
            }
            res &= (rr[bit] == u[bit] * h - c[bit] * y_ij_view[bit]);
            if rr[bit] != u[bit] * h - c[bit] * y_ij_view[bit]{
                println!("rr=h^u/y^c wrong for i={}, j={}, bit={}", i, j, bit);
            }
        }
        let chal_ij = c[l-1];
        chal_aggregated += chal_ij;
        cursor += 1;
    }

    let mut rr_agg = Vec::with_capacity(possible_ij_set_length * l);
    let mut y_agg  = Vec::with_capacity(possible_ij_set_length * l);

    let mut buf = 0;
    for (i, j) in &possible_ij_set {
        let proof = proofs[buf].clone();
        let rr = proof.commitments;
        for x in &rr {
            rr_agg.push(*x);
        }

        for d_ij in &y[i*a + j][offset..] {
            y_agg.push(*d_ij);
        }
        buf += 1;
    }

    let chal = chal_list(&rr_agg.clone(), &y_agg.clone(), &vec![h; possible_ij_set_length*l]);
    res &= chal == chal_aggregated;
    println!("challenge sum verified ? {}", chal==chal_aggregated);
    res
}

pub fn measure_time_comp_similarity(
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
        let proofs = prove_comp_similarity(threshold, d_private_vec, n, m, u, &c_vec_refs, &w_refs, h, &mut rng_proof);
        let duration_proof_threshold = t2.elapsed();
        time_proof_threshold += duration_proof_threshold;
        println! ("Proof Threshold : {:?}", duration_proof_threshold);

        let t3 = Instant::now();
        let res = verify_similarity(n, m, u, &proofs, &c_vec_refs, h, threshold);
        let duration_verify_threshold = t3.elapsed();
        time_verify_threshold += duration_verify_threshold; 
        println! ("Verify Threshold : {:?}", duration_verify_threshold);

        println!("==== Verify for Threshold : {} ==== ", res);
    }

    println!("==== Timing over {} iterations ====", iter);
    println!("  setup:         {:?}", time_setup/(iter as u32));
    println!("  commit:        {:?}", time_commit/(iter as u32));
    println!("  proof (square):   {:?}", time_proof_square/(iter as u32));
    println!("  verify (square):  {:?}", time_verify_square/(iter as u32));
    println!("  proof (distance):   {:?}", time_proof_distance/(iter as u32));
    println!("  verify (distance):  {:?}", time_verify_distance/(iter as u32));
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

