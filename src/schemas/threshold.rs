use rand::rngs::OsRng;
use rand_core::{ CryptoRng, RngCore, CryptoRngCore };   
use std::time::{ Instant, Duration }; 
use curve25519_dalek::{ scalar::Scalar, RistrettoPoint, traits::Identity};
use zeroize::Zeroize;
use crate::usefulstructs::*;
use crate::usefulfuncs::{random_ecg, random_ristretto_point, random_scalar, chal_single_proof_square, chal_distance, random_vec_scalar, lincomb_pow2, two_pow, scalar_to_bits, compute_mpd_with_window_scalar, chal_list};

use crate::commit::*;

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
    // println!("l = {}", l);
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
    for ind in epsilon_bin[last]-offset+1..l{
        // println!("{}", ind);
        if y_view[ind] == alpha_view[ind] * h{
            // println!("enter in the first or");
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
                    for _ in 0..t{
                        list_relation[t] = false;
                    }
                    break;
                }
            }
        }
    }

    // deduce the first true relation from right
    while list_relation[first]==false{
        first+=1;
    }
    // generate vlidation list for epsilon_bin
    let mut list_epsilon_bool : Vec<bool> = vec![false; l];
    for bit in epsilon_bin{
        list_epsilon_bool[bit-offset] = true;
    }


    // commitment phase
    for i in 0..l{
        if list_relation[i]{
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
            if list_relation[i]==false{
                c[i] = random_scalar(rng);
                c_sum += c[i];
                rr[i] = u[i] * h - c[i] * y_view[i];
            }
        }
        let chal_gen = chal_list(&rr.clone(),&y_view,&vec![h;l]);
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
    let chal_gen = chal_list(&rr.clone(),&y_view,&vec![h;l]);

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
    for i in first+1..alpha_1_bit{
        if list_relation[i] && list_epsilon_bool[i] && i>1{
            let mut c_sum = Scalar::ZERO;
            for j in i+1..alpha_bit+1{
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
	let chal_gen = chal_list(&rr.clone(),&y_view,&vec![h;l]);
	
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

pub fn verify_threshold(
    h: &RistrettoPoint,
    y_list: &[Vec<RistrettoPoint>],
    proof_list: &[ZKthresholdi],
    epsilon_bin: &[usize]
)->bool{
    let mut res : bool = true;
    let l = y_list.len();
    for i in 0..l{
        let y = &y_list[i];
        let proof_ref = &proof_list[i];
        res &= verify_threshold_i(proof_ref, y.clone(), h.clone(), epsilon_bin);
        
    }
    res
}

pub fn measure_time_threshold(
    upper: usize,
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
        // let mut rng_dist  = OsRng;

        // --- 1) Compute MPD(i) for each i -------------------------------
        let ts = random_ecg(&mut rng, n, upper);
        let mpd = compute_mpd_with_window_scalar(&ts, m); // length a
        // println!("{:?}", mpd);
        // Binary decomposition MPD_i -> {MPD_{i,u}}_{u=0..ell-1}
        let mpd_bits: Vec<Vec<Scalar>> = mpd
            .iter()
            .map(|val| scalar_to_bits(val, ell)) // each is length ell, bits 0/1 as Scalar
            .collect();

        // --- 2) Setup ----------------------------------------------------
        let t0 = Instant::now();
        let set = setup(n, &mut rng);
        time_setup += t0.elapsed();

        let g = set.gen;
        let h = set.h_;
        // let n_set = set.n_;

        // --- 3) Commit original time series (for distances etc.) --------
        let t1 = Instant::now();

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
        // println!("{:?}", epsilon_bin);

        time_commit += t1.elapsed();

        // println!("  commit:        {:?}", time_commit);

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

        // println!("  proof (MIN):   {:?}", time_proof_threshold);

        // --- 7) VERIFY time ---------------------------------------------
        let t_verify = Instant::now();
        let ok = verify_threshold(
            &h,
            &Y_list,
            &proof_list,
            &epsilon_bin
        );

        time_verify_threshold += t_verify.elapsed();
        // println!("  verify (THRESHOLD):  {:?}", time_verify_threshold);

        println!("{:?}",ok);
        debug_assert!(ok, "verify_threshold failed!");
    }

    println!("==== THRESHOLD timing over {} iterations ====", iter);
    println!("  setup:         {:?}", time_setup/(iter as u32));
    println!("  commit:        {:?}", time_commit/(iter as u32));
    println!("  proof (Threshold):   {:?}", time_proof_threshold/(iter as u32));
    println!("  verify (Threshold):  {:?}", time_verify_threshold/(iter as u32));
}