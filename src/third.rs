pub fn Proof_exit_bin<T: CryptoRng + RngCore>(
    set: &Set,
    l: Scalar, // length of binary bits
    a: Scalar, // length of matrix profile
    i: Scalar, // proof that a distance exists among all the distances with si
    m_i: &[RistrettoPoint], // pederson commitment of the value MPD_i in bits
    d_ij: &[RistrettoPoint], // pederson commitement of distance si and sj
    z_i: &[Scalar], // secret key to open M_i
    w_ij: &[Scalar] // secret key to open D_ij
    rng_proof: &mut T
)->ProofExistij{
    let r_i : Vec<RistrettoPoint> = Vec::with_capacity(a * l);
    let res_i : Vec<RistrettoPoint> = Vec::with_capacity(a * l);
    let c_i : Vec<Scalar> = Vec::with_capacity(a);
    let y_i : Vec<Scalar> = Vec::with_capacity(a * l);
    let h = set.h;
    let isj_found : mut bool = false;
    let index_j_star : usize = 0;
    let isj : mut bool = true;
    let c_accum : Scalar = Scalar::ZERO;

    // find the index j star
    let j : usize = 0;
    while !isj_found{
        isj = true;
        for u in 0..l{
            let alpha_u = z_i[u] - w_ij[j*l+u];
            let y_u = m_i[u] - d_ij[j*l+u];
            if y_u != h * alpha_u{
                isj = false;
                break;
            }
        }
        if isj{
            index_j_star = j;
            isj_found = true;
        }
        j += 1;
    }
    
    for j in 0..a{
        if j == index_j_star{
            // proof
            for u in 0..l{
                let alpha_u = z_i[u] - w_ij[j*l+u];
                let y_u = m_i[u] - d_ij[j*l+u];
                y_i.push(y_u);
                let r = random_scalar(rng_proof);
                let r_ju = h * r;
                r_i.push(r_ju);
                res_i.push(Scalar::ZERO); // replace by the real res after
            }
            // put 0 to the challenge
            c_i.push(Scalar::ZERO);
        }else{
            // simulate
            let c_j = random_scalar(rng_proof);
            c_i.push(c_j);
            c_accum += c_j;
            for u in 0..l{
                let alpha_u = z_i[u] - w_ij[j*l+u];
                let y_u = m_i[u] - d_ij[j*l+u];
                y_i.push(y_u);
                let r = random_scalar(rng_proof);
                let res_ju = random_scalar(rng_proof);
                res_i.push(res_ju);
                r_iu = h * res_i - c_j * y_u;
                r_i.push(r_iu);
            }
        }
    } 
    // A challenge distance function that takes a list
    // then calculate the c, and deduce c_j_star = c - c_accum
    // replace the res_i for the indices index_j_star to index_j_star * l to the real res
    let g_list : Vec<RistrettoPoint> = Vec::with_capacity(a*u);
    for _ in 0..a*u{
        g_list.append(h);
    }
    let c = chal_list(&c_i, &y_i, &g_list);
    let c_j_star = c-c_accum;
    c_i[index_j_star] = c_j_star;
    for u in 0..l{
        res_j_star_u = r_i[index_j_star*l+u]+(z_i[u]-w_ij[index_j_star*l+u])*c_j_star;
        res_i[index_j_star*l+u] = res_j_star_u;
    }
    return ProofExistij{r_i: r_i, c_i: c_i, z_i:res_i}
}

pub fn verify_exit_bin(
    m_i: &[RistrettoPoint],
    d_ij: &[RistrettoPoint],
    l: usize, // length of bits
    a: usize, // length of m_i
    set: &Set,
    proofs_exit: &[ProofExistij]
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
            let r_i = proofs_exit.r_i[j*l+u];
            let c_i = proofs_exit.c_i[i];
            let z_i = proofs_exit.z_i[j*l+u];
            res &= (h * z_i == r_i + y_u*c_i);
        }
    }
    // verify c
    let c = chal_list(&proofs_exit.r_i, &y_i, &g_i);
    let mut c_to_test : Scaler = Scalar::ZERO;
    for c_i in proofs_exit.c_i{
        c_to_test += c_i;
    }
    res &= (c_to_test == c);
    res
}