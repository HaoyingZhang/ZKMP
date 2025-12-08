use rand::rngs::OsRng;
use rand_core::{ CryptoRng, RngCore, CryptoRngCore };   
use std::time::{ Instant, Duration }; 
use curve25519_dalek::{ scalar::Scalar, RistrettoPoint, traits::Identity};
use zeroize::Zeroize;
use crate::usefulstructs::*;
use crate::usefulfuncs::{random_ecg, random_ristretto_point, random_scalar, chal_single_proof_square, chal_distance, random_vec_scalar, lincomb_pow2, two_pow, scalar_to_bits, compute_mpd_with_window_scalar, chal_list};

use crate::commit::*;

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

    while cursor>=0 && res==false{
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
                res = false;
                break;
            }

        }
        cursor -= 1;
    }
    res
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_relation_check() {
        let rel_list = vec![false, true, true, true, true];
        let l = 5;
        let u_alpha = vec![2,3,4];
        let res = relation_check(&rel_list, l, &u_alpha);
        assert_eq!(res, true);
        println!("Test relation check passed !");
    }
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
                    rel_list_j_star[j] = j == t;
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
        // println!("calculated sum challenge for index: {}", u_alpha_view[1]);
        c_j_star[u_alpha_view[1]] = buffer_sum;
        rr_j_star[u_alpha_view[1]] = u_j_star[u_alpha_view[1]] * h  - c_j_star[u_alpha_view[1]] * d_ij_star_view[u_alpha_view[1]];

        let mut end = 2;
        while end < u_alpha_view.len() && u_alpha_view[end]<=nearest_alpha_index_right {
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
            // println!("calculated sum challenge for index: {}", u_alpha_view[end]);
            c_j_star[u_alpha_view[end]] = buffer_sum + c_j_star[u_alpha_view[end-1]];
            rr_j_star[u_alpha_view[end]] = u_j_star[u_alpha_view[end]] * h - c_j_star[u_alpha_view[end]] * d_ij_star_view[u_alpha_view[end]];
            end += 1;
        }
        // calculate the random for indices from index_right to index_left
        for i in nearest_alpha_index_right+1..nearest_alpha_index_left{
            // println!("Entrer ici: nearest_alpha_index_right = {}, left = {}", nearest_alpha_index_right, nearest_alpha_index_left);
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
        if nearest_alpha_index_left == l && rel_list_j_star[nearest_alpha_index_left-1]==false{
            let _ = simulate_c_and_rr(
                    nearest_alpha_index_left,
                    &mut c_j_star, 
                    &mut rr_j_star, 
                    &d_ij_star_view, 
                    &u_j_star, 
                    h,
                    rng_proof);
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
        // println!("Entered in this block!"); 
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
        c[end] = sum_buffer + c[begin-1];
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

    // let alpha = epsilon_bin[epsilon_bin.len()-1]-offset;
	
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

    res &= (chal == chal_aggregated);

    res
}

pub fn measure_time_comp(
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

        let (_, _, x_diff, k_diff, k_tilde) = calculate_inner_diff_commit(&c, &set, &mut rng_proof);
        
        let _t1 = Instant::now();
        let (d_vec, _, w_vec, _) = calculate_dist_commit(&mut rng_proof, n, m, ell, g, h, &x_diff, &k_diff, &k_tilde);

        // calculate u_alpha list
        let epsilon_bin_val = scalar_to_bits(&Scalar::from(epsilon), ell);
        let mut epsilon_bin : Vec<usize> = Vec::with_capacity(ell);
        for bit in 0..epsilon_bin_val.len(){
            if epsilon_bin_val[bit] == Scalar::ZERO{
                epsilon_bin.push(bit);
            }
        }

        time_commit += _t1.elapsed();

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