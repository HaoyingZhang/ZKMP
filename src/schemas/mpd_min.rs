use rand::rngs::OsRng;
use rand_core::{ CryptoRng, RngCore, CryptoRngCore };   
use std::time::{ Instant, Duration }; 
use curve25519_dalek::{ scalar::Scalar, ristretto::RistrettoPoint, traits::Identity};
use zeroize::Zeroize;
use crate::usefulstructs::*;
use crate::usefulfuncs::{random_ecg, random_ristretto_point, random_scalar, chal_single_proof_square, chal_distance, random_vec_scalar, lincomb_pow2, two_pow, scalar_to_bits, compute_mpd_with_window_scalar, chal_list};

use crate::commit::*;

// -------------- MPD min -------
// pub fn list_relation(
//     mut cmpt: usize,
//     mpd_bin: Vec<Scalar>,
//     d_ij: &[Scalar],
//     mut found: bool,
//     mut list: Vec<bool>
// ) -> Vec<bool>{
// 	while (found == false) && (cmpt > 0){
// 		if d_ij[cmpt-1] - mpd_bin[cmpt-1] == Scalar::ONE {
// 			list[2*cmpt-1] = true; // corresponds to y_{2l}
// 			found = true;
// 		}
// 		else{
// 			list[2*cmpt-2] = true; // corresponds to y_{2l-1}	
// 			cmpt = cmpt - 1;
// 			list_relation(cmpt,mpd_bin.clone(),d_ij.clone(),found,list.clone());
// 		}
// 	}
//     // println!("cmpt = {}", cmpt);
// 	return list;
// }
pub fn list_relation(
    mpd_bin: Vec<Scalar>,
    d_ij: &[Scalar],
    ell: usize
) -> Vec<bool>{
    let mut cmpt = ell;
    let mut list: Vec<bool> = vec![false; 2*ell];
	while cmpt > 0{
		if d_ij[cmpt-1] - mpd_bin[cmpt-1] == Scalar::ONE {
			list[2*cmpt-1] = true; // corresponds to y_{2l-1}
            break;
		}
		else{
			list[2*cmpt-2] = true; // corresponds to y_{2l}	
			cmpt = cmpt - 1;
		}
	}
    // println!("cmpt = {}", cmpt);
	return list;
}


// function for a given i
pub fn prove_min<T: CryptoRng + RngCore>(rng: &mut T, y: &[RistrettoPoint],h: RistrettoPoint,mut alpha: &[Scalar],mut list: Vec<bool>) -> ZKmin{
	let l = y.len() / 2;
	let mut r: Vec<Scalar> = vec![Scalar::from(0u64);2*l]; // vector of random 
	let mut rr: Vec<RistrettoPoint> = vec![RistrettoPoint::identity();2*l]; // vector of commitments
	let mut c: Vec<Scalar> = vec![Scalar::from(0u64);2*l]; // vector of challenges
	let mut u: Vec<Scalar> = vec![Scalar::from(0u64);2*l]; // vector of responses
	
	let mut first = 0;
	while list[first] == false{
		first +=1;
	}
    // println!("{:?}", list);
	
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
	let chal_gen = chal_list(&rr.clone(),&y,&vec![h;2*l]);
	
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
	
	// alpha.zeroize();
	// r.zeroize();
	// list.zeroize();
	
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
        println!("Challenge error");
		return false
	}
    for i in 2..l{
		if c[2*i-2] != c[2*i-3] + c[2*i-4]{
			println!("{:?}, {}",c[2*i-2] == c[2*i-3] + c[2*i-4],i);
			return false
		}
	}
	for i in 0..2*l-1{
		if rr[i] != u[i] * h - c[i] * y[i]{
            println!("Error at indice {}", i);
			return false	
		}
	}
	
	return true
}


pub fn proof_mpd_min<T: CryptoRngCore>(
    mpd_bin: Vec<Vec<Scalar>>, // [MPD_i_binary]
    d_ij: &[&[Scalar]], // [d_i_j_binary]
    h: &RistrettoPoint,
    l: usize, // l = n-m+1, length of MPD
    _k: usize,
    m: usize,
    alpha_list: &[&[Scalar]], // list of secrets
    y_list: &[&[RistrettoPoint]], // list of commitments
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

                // let mut list = vec![false;rels];
                // let cmpt = k_local;
                // let found = false;

                // let t_list = Instant::now();
    	        // let list = list_relation(cmpt, mpd_bin[i].clone(), d_ij[i*l+j].clone(), found, list);
                let list = list_relation(mpd_bin[i].clone(), d_ij[i*l+j], k_local);
                // println!("Time list relation: {:?}",t_list.elapsed());
                // println!("{:?}", list);
                // let t_prove = Instant::now();
                let proof = prove_min(proof_rng, y, h.clone(), alpha.clone(), list.clone());
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
    upper: usize,
    n: usize,   // length of time series
    m: usize,   // window size
    ell: usize, // number of bits (ℓ)
    iter: usize,
) {
    // let a = n - m + 1; // number of MPD entries (indices i ∈ I

    let mut time_setup      = Duration::ZERO;
    let mut time_commit     = Duration::ZERO;
    let mut time_proof_mpd  = Duration::ZERO;
    let mut time_verify_mpd = Duration::ZERO;

    for _ in 0..iter {
        let mut rng       = OsRng;
        let mut rng_k     = OsRng;
        let mut rng_proof = OsRng;
        // let mut rng_dist  = OsRng;

        let t0 = Instant::now();
        let mut set = setup(n, &mut rng);
        time_setup += t0.elapsed();

        // --- 1) Compute MPD(i) for each i -------------------------------
        let ts = random_ecg(&mut rng, n, upper);
        // println!("{:?}", ts);

        let t1 = Instant::now();
        let commitment = commit(&mut set, &ts.to_vec(), &mut rng_k);

        // let x = &commitment.x_;
        // let k = &commitment.k_;
        let n = set.n_;
        let g = set.gen;
        let h = set.h_;

        // calculate commit
        let (_, _, x_diff, k_diff, k_tilde) = calculate_inner_diff_commit(&commitment, &set, &mut rng_proof);
        
        let (d_vec, _, w, d_private_vec) = calculate_dist_commit(&mut rng_proof, n, m, ell, g, h, &x_diff, &k_diff, &k_tilde);
        
        // MPD
        let mpd      = compute_mpd_with_window_scalar(&ts, m);
        let mpd_bin: Vec<Vec<Scalar>> = mpd.iter().map(|x| scalar_to_bits(x, ell)).collect();

        let (m_vec, _, z_vec) = calculate_mpd_commit(&g, &h, mpd_bin.clone(), ell, &mut rng_proof);

        let m_vec_refs: Vec<&[RistrettoPoint]> = m_vec.iter().map(|inner| inner.as_slice()).collect();
        let z_vec_refs: Vec<&[Scalar]> = z_vec.iter().map(|inner| inner.as_slice()).collect();
        let d_vec_refs: Vec<&[RistrettoPoint]> = d_vec.iter().map(|inner| inner.as_slice()).collect();
        let w_refs : Vec<&[Scalar]> = w.iter().map(|inner| inner.as_slice()).collect();
        let d_private_refs : Vec<&[Scalar]> = d_private_vec.iter().map(|inner| inner.as_slice()).collect();

        // println!("MPD: {:?}", mpd);
        let a = mpd.len();
        
        let mut alpha_list : Vec<Vec<Scalar>> = Vec::with_capacity(a*a);
        let mut y_list : Vec<Vec<RistrettoPoint>> = Vec::with_capacity(a*a);

        for i in 0..a{
            for j in 0..a{
                let mut alpha_buffer : Vec<Scalar> = Vec::with_capacity(2*ell);
                let mut y_buffer : Vec<RistrettoPoint> = Vec::with_capacity(2*ell);
                for bit in 0..ell{
                    let alpha_i_ell_ = z_vec_refs[i][bit] - w_refs[i*a+j][bit];
                    alpha_buffer.push(alpha_i_ell_);
                    alpha_buffer.push(alpha_i_ell_);
                    let y_buffer_pair_ = m_vec_refs[i][bit] - d_vec_refs[i*a+j][bit];
                    let y_buffer_impair_ = m_vec_refs[i][bit] - d_vec_refs[i*a+j][bit] + g;
                    y_buffer.push(y_buffer_pair_);
                    y_buffer.push(y_buffer_impair_);
                }
                alpha_list.push(alpha_buffer.clone());
                y_list.push(y_buffer.clone());
            }
        }

        let y_list_refs: Vec<&[RistrettoPoint]> = y_list.iter().map(|inner| inner.as_slice()).collect();
        let alpha_list_refs : Vec<&[Scalar]> = alpha_list.iter().map(|inner| inner.as_slice()).collect();


        let tak = t1.elapsed();
        time_commit += tak;
        println!("Commit time {:?}", tak);

        // initiate is_real_relation list
        let is_real_relation = vec![false; 2 * ell];

        // --- 6) PROOF time ----------------------------------------------
        let t_proof = Instant::now();
        let proof_list = proof_mpd_min(
            mpd_bin.clone(),
            &d_private_refs,
            &h,
            a,              // l = number of indices
            ell,            // k = number of bits per index (or your tree depth parameter)
            m,            
            &alpha_list_refs,
            &y_list_refs,
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