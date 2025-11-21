pub fn list_relation(mut cmpt: usize,y: Vec<RistrettoPoint>,h: RistrettoPoint,alpha: Vec<Scalar>,mut found: bool,mut list: Vec<bool>) -> Vec<bool>{
	while (found == false) && (cmpt > 0){
		if y[2*cmpt-1] == alpha[2*cmpt-1] * h{
			list[2*cmpt-1] = true; // corresponds to y_{2l}
			found = true;
		}
		else{
			list[2*cmpt-2] = true; // corresponds to y_{2l-1}	
			cmpt = cmpt - 1;
			list_relation(cmpt,y.clone(),h,alpha.clone(),found,list.clone());
		}
	}
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
	let chal_gen = chal_list(rr.clone(),y.clone(),vec![h;2*l]);
	
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

pub fn verify_min(proof: ZKmin, y: Vec<RistrettoPoint>,h: RistrettoPoint) -> bool{
	
	// Parses the proof
	let rr = proof.commitments;
	let c = proof.challenges;
	let u = proof.responses;
	
	let l = y.len() / 2;
	
	// Recomputes the general challenge
	let chal_gen = chal_list(rr.clone(),y.clone(),vec![h;y.len()]);
	
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

proof_mpd_min<T: CryptoRngCore + ?Sized>(
    h: &RistrettoPoint,
    l: usize, 
    k: usize,
    m: usize,
    alpha_list: &[[Scalar]],
    y_list: &[RistrettoPoint],
    proof_rng: &mut T,
    is_real_relation: &[bool]
)->&[ZKmin]{
    let proof_list : Vec<Option<ZKmin>> = Vec::with_capacity(l*l);
    for i in 0..l{
        for j in 0..l{
            if i.abs_diff(j) <= m/2{
                proof_list.push(None);
                continue;
            }
            else{
                alpha = alpha_list[i*l+j];
                y = y_list [i*l+j];
                let mut list = vec![false;2*k];
                let mut cmpt = k;
                let mut found = false;
    	        list = list_relation(cmpt,y.clone(),h.clone(),alpha.clone().clone(),found,list.clone());
                let proof = prove_min(proof_rng, y, h, alpha, list);
                proof_list.push(proof);
            }
        }
    }
    &proof_list
}