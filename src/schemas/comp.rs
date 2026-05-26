use rand::rngs::OsRng;
use rand_core::{ CryptoRng, RngCore, CryptoRngCore };   
use std::time::{ Instant, Duration };
use std::io::Write;
use curve25519_dalek::{ scalar::Scalar, RistrettoPoint, traits::Identity};
use zeroize::Zeroize;
use crate::usefulstructs::*;
use crate::usefulfuncs::{scalar_to_u64, random_ecg, random_ristretto_point, random_scalar, chal_single_proof_square, chal_distance, random_vec_scalar, lincomb_pow2, two_pow, scalar_to_bits, compute_mpd_with_window_scalar, chal_list};

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
        if cursor >0 {
            cursor -= 1;
        }
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
        let offset = u_alpha[0];
        let u_alpha_view : Vec<usize> = u_alpha.iter().map(|val| val-offset).collect();
        let rel_list_view = &rel_list[offset..];
        let res = relation_check(&rel_list_view, l-offset, &u_alpha_view);
        assert_eq!(res, true);
        println!("Test relation check passed !");
    }
}

pub fn prove_non_anomaly_i<T: CryptoRngCore>(
    thr: u64, // threshold
    dist_vec: &[Scalar], // private distances of d_ij
    u_alpha: &[usize], // zero bits indices
    d_vec: &[&[RistrettoPoint]], // D_iju the commitments of d_iju
    w_vec: &[&[Scalar]], // w_iju the secret key of d_iju
    h: RistrettoPoint,
    rng_proof: &mut T
)->Vec<ZKthresholdi>{
    let a = d_vec.len(); //number of j
    // println!("length of j {}", a); 
    let offset = u_alpha[0];
    let u_alpha_view : Vec<usize> = u_alpha.iter().map(|val| val-offset).collect();
    let alpha = u_alpha_view.len() - 1;
    // println!("u alpha : {:?}", u_alpha_view);
    let l = d_vec[0].len() - offset; // bit length
    let mut d_ij : &[RistrettoPoint];
    let mut w_ij : &[Scalar];
    let mut j_star = a; // when no j_star found
    for j in 0..a{
        if scalar_to_u64(dist_vec[j]) < thr{
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
            let (proof_j, chal_j) = simulate_pi_0(&u_alpha_view, &d_vec[j][offset..], h, rng_proof);
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
    let mut stop_term = None;

    for index in (0..alpha+1).rev() {
        let ind = u_alpha_view[index];
        if d_ij_star_view[ind] == w_ij_star_view[ind] * h {
            stop_term = Some(ind);
            break;
        }
    }
    let stop_term = stop_term.expect("No true term in the ij star");
    // println!("stop term = {}", stop_term);

    // generate the alea 
    // for i in 0..l{
    //     if rel_list_j_star[i]{
    //         r_j_star[i] = random_scalar(rng_proof);
    //         rr_j_star[i] = r_j_star[i] * h;
    //     }else{
    //         u_j_star[i] = random_scalar(rng_proof);
    //     }
    // }

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

    // check if all the term has a rr replaced
    // for i in 0..l{
    //     assert!(rr_j_star[i]!=RistrettoPoint::identity());
    // }

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

    // complete
    if stop_term == 0{
        let mut c_current = chal_j_star;
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
        let mut c_current = chal_j_star;
        let mut end_ind = alpha;

        // 1. Fill the Right side (stop_term + 1 to l)
        for i in (stop_term + 1..l).rev() {
            if i == u_alpha_view[end_ind] {
                c_current -= c_j_star[i];
                end_ind -= 1;
            } else {
                c_j_star[i] = c_current;
                u_j_star[i] = r_j_star[i] + c_j_star[i] * w_ij_star_view[i];
            }
        }

        // 2. Set the Bridge (stop_term)
        c_j_star[stop_term] = c_current - c_current_right;
        u_j_star[stop_term] = r_j_star[stop_term] + c_j_star[stop_term] * w_ij_star_view[stop_term];

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

// simulation proof
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

pub fn verify_non_anomaly_j(
    proof: &ZKthresholdi, 
    y: Vec<RistrettoPoint>,
    h: RistrettoPoint,
    epsilon_bin: &[usize]) -> bool{
	
	// Parses the proof
	let rr = &proof.commitments;
	let c = &proof.challenges;
	let u = &proof.responses;
    let alpha = epsilon_bin.len()-1;

    let offset = epsilon_bin[0];

    // let alpha = epsilon_bin[epsilon_bin.len()-1]-offset;
	
	let l = y.len()-offset;
	
	// Recomputes the general challenge
    let y_view = &y[offset..];  

	let mut res = true;
	let mut cursor = 1;
    let mut c_current = c[0];
    for i in 0..l{
        if cursor <= alpha && i == epsilon_bin[cursor]{
            c_current += c[i];
            cursor += 1;
        }
        else{
            res &= c[i] == c_current;
            if res == false{
                println!("challenge bit wrong for bit = {}", i);
            }
        }
    }

    for i in 0..l{
		res &= rr[i] == u[i] * h - c[i] * y_view[i];
        if res == false{
            println!("condition verification failed for bit = {}", i);
        }
	}
	return res
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
    let alpha = u_alpha_view.len()-1;
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
        let d_ij_view = &d_ij[offset..];

        let verify_j = verify_non_anomaly_j(&proof_j, d_ij_view.to_vec(), h, &u_alpha_view);
        if verify_j == false{
            println!("error j = {}", j);
        }
        res &= verify_j;

        // if verify_j == false{
        //     println!("Error in verify threshold i for j = {}", j);
        // }
        let mut cursor = 1;
        let mut cj = c_j[0];
        for bit in 0..l{
            if cursor <= alpha && bit == u_alpha_view[cursor]{
                cj += c_j[bit];
                cursor += 1;
            }
        }
        chal_aggregated += cj;
        

        for rr in rr_j{
            rr_aggregated.push(rr.clone());
        }

        for y in d_ij_view{
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

    for _i in 0..iter {
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
        
        let (d_vec, _, w_vec, _, d_private_vec) = calculate_dist_commit(&mut rng_proof, n, m, ell, g, h, &x_diff, &k_diff, &k_tilde);

        
        // calculate u_alpha list
        let epsilon_bin_val = scalar_to_bits(&Scalar::from(epsilon), ell);
        let mut epsilon_bin : Vec<usize> = Vec::with_capacity(ell);
        for bit in 0..epsilon_bin_val.len(){
            if epsilon_bin_val[bit] == Scalar::ONE{
                epsilon_bin.push(bit);
            }
        }
        
        let a = n - m + 1;
        let half_m = m/2;
        let mut verify_non_anomaly : bool = true;
        let mut proof_size : u64 = 0;

        for i in 0..a {

            let t2 = Instant::now();
            
            // println!("i = {}", i);
            let mut d_i_refs: Vec<&[RistrettoPoint]> = Vec::new();
            let mut w_i_refs: Vec<&[Scalar]> = Vec::new();
            let mut d_private_i_refs : Vec<Scalar> = Vec::new();
            let left_end = i.saturating_sub(half_m);
            for j in 0..left_end {
                d_i_refs.push(d_vec[i * a + j].as_slice());
                w_i_refs.push(w_vec[i * a + j].as_slice());
                d_private_i_refs.push(d_private_vec[i * a + j]);
            }

            let right_start = (i+half_m+1).min(a);
            for j in right_start..a {
                d_i_refs.push(d_vec[i * a + j].as_slice());
                w_i_refs.push(w_vec[i * a + j].as_slice());
                d_private_i_refs.push(d_private_vec[i * a + j]);
            }

            // --- Prove ---
            
            let proof_i = prove_non_anomaly_i(
                epsilon,
                &d_private_i_refs,
                &epsilon_bin,
                &d_i_refs,
                &w_i_refs,
                h,
                &mut rng_proof
            );
            time_proof_non_anomaly += t2.elapsed();

            if _i == 0 {
                std::fs::create_dir_all("proofs_script").unwrap();
                let path = format!("proofs_script/proof_comp_{}.bin", i);
                let mut file = std::fs::File::create(&path).expect("failed to create proof file");
                for p in &proof_i {
                    for c in &p.commitments { file.write_all(c.compress().as_bytes()).unwrap(); }
                    for c in &p.challenges  { file.write_all(c.as_bytes()).unwrap(); }
                    for r in &p.responses   { file.write_all(r.as_bytes()).unwrap(); }
                }
                drop(file);
                let size = std::fs::metadata(&path).unwrap().len();
                proof_size = proof_size + size;
            }

            // --- Verify ---
            let t3 = Instant::now();
            let res = verify_non_anomaly_i(
                proof_i,
                &epsilon_bin,
                &d_i_refs,
                h
            );
            verify_non_anomaly &= res;
            time_verify_non_anomaly += t3.elapsed();
        }
        println!("verify: {}", verify_non_anomaly);
        if _i == 0{
            println!("proof_comp.bin size: {} bytes ({:.2} KB)", proof_size, proof_size as f64 / 1024.0);
        }

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