#[allow(unused_imports)]
#[allow(unused_variables)]
use rand::rngs::OsRng;
use rand_core::{ CryptoRng, RngCore, CryptoRngCore };   
use std::time::{ Instant, Duration }; 
use curve25519_dalek::{ scalar::Scalar, RistrettoPoint, traits::Identity};
use zeroize::Zeroize;
use crate::usefulstructs::*;
use crate::usefulfuncs::{random_ecg, random_ristretto_point, random_scalar, chal_single_proof_square, chal_distance, random_vec_scalar, lincomb_pow2, two_pow, scalar_to_bits, compute_mpd_with_window_scalar, chal_list};

// Generate a setup set:
pub fn setup<T: CryptoRng + RngCore>(n: usize, rng: &mut T) -> Set {
    let generator = random_ristretto_point(rng);
    let h = random_ristretto_point(rng);
    let set = Set{gen: generator, h_: h, n_: n};  
    return set;   
}

// Generate a commitment:
pub fn commit<T: CryptoRng + RngCore>(
    s: &mut Set,
    time_series: &Vec<Scalar>, 
    rng_k: &mut T
) -> Commit {
    let gen = s.gen;
    let h = s.h_;

    let mut k: Vec<Scalar> = Vec::new();
    let mut c: Vec<RistrettoPoint> = Vec::new();
    let mut x_s: Vec<Scalar> = Vec::new();

    for i in time_series {
        let k_i = random_scalar(rng_k);
        let c_i = i*gen + &k_i*h;
        c.push(c_i);
        k.push(k_i);
        x_s.push(*i);
    }
    let commit = Commit{k_: k, x_: x_s, c_: c};
    return commit;
}

// Open a commitment:
pub fn open(c: &Commit) -> &Vec<Scalar>{
    let res = &c.x_;
    return res;
}

pub fn calculate_inner_diff_commit<T: CryptoRng + RngCore>(
    commitment: &Commit,
    set: &Set,
    rng: &mut T
)->(Vec<RistrettoPoint>,Vec<RistrettoPoint>,Vec<Scalar>,Vec<Scalar>,Vec<Scalar>){

    let c_pub = &commitment.c_;
    let k = &commitment.k_;
    let x = &commitment.x_;

    // let g = set.gen;
    let h = set.h_;

    let n = set.n_;

    let mut c_diff: Vec<RistrettoPoint> = Vec::with_capacity(n*n);
    let mut c_tilde : Vec<RistrettoPoint> = Vec::with_capacity(n*n);
    let mut x_diff: Vec<Scalar> = Vec::with_capacity(n*n);
    let mut k_diff: Vec<Scalar> = Vec::with_capacity(n*n);
    let k_tilde = random_vec_scalar(rng, n*n);
    
    for i in 0..n{
        for j in 0..n{
            let c_ij = c_pub[i] - c_pub[j];
            let x_ij = x[i] - x[j];
            let k_ij = k[i] - k[j];
            let k_ij_tilde = k_tilde[i*n+j];
            let c_ij_tilde = x_ij * c_ij + k_ij_tilde * h;

            c_tilde.push(c_ij_tilde);
            x_diff.push(x_ij);
            k_diff.push(k_ij);
            c_diff.push(c_ij);
        }
    }
    (c_diff, c_tilde, x_diff, k_diff, k_tilde)

}

pub fn calculate_dist_commit<T: CryptoRng + RngCore>(
    rng_proof: &mut T,
    n: usize,
    m: usize,
    u: usize,
    g: RistrettoPoint,
    h: RistrettoPoint,
    x_diff: &[Scalar],
    k_diff: &[Scalar],
    k_tilde: &[Scalar],
)->(Vec<Vec<RistrettoPoint>>, Vec<Vec<RistrettoPoint>>, Vec<Vec<Scalar>>, Vec<Vec<Scalar>>, Vec<Scalar>){
    // number of subsequences
    let l = n - m + 1;
        
    let mut c_vec : Vec<Vec<RistrettoPoint>> = Vec::with_capacity(l*l);
    let mut c_bis_vec : Vec<Vec<RistrettoPoint>> = Vec::with_capacity(l*l);
    let mut d_private_bin_vec: Vec<Vec<Scalar>> = Vec::with_capacity(l*l);
    let mut w : Vec<Vec<Scalar>> = Vec::with_capacity(l*l);
    let mut d_private_vec: Vec<Scalar> = Vec::with_capacity(l*l);

    for i in 0..l{
        for j in 0..l{
            let mut wij = Scalar::ZERO;
            let mut dij = Scalar::ZERO; // compute only once, never used after in other proofs

            // accumulate over window m
            for r in 0..m {
                let xij = x_diff[(i + r) * n + (j + r)]; // x[i + r] - x[j + r];
                let kij = k_diff[(i + r) * n + (j + r)]; // k[i + r] - k[j + r];
                let k_tilde_ij = k_tilde[(i + r) * n + (j + r)];
                wij += xij * kij + k_tilde_ij;
                dij += xij * xij;
            }
            let dij_bin = scalar_to_bits(&dij, u);

            // sample u-1 random public shares for wij and set the last to match sum
            let mut wij_pub: Vec<Scalar> = Vec::with_capacity(u);
            for _ in 0..(u - 1) {
                wij_pub.push(random_scalar(rng_proof));
            }
            let first = lincomb_pow2(&wij_pub);
            let denom = two_pow(u - 1); // 2^(u-1)
            let last = (wij - first) * denom.invert(); // division with scalar
            wij_pub.push(last);

            let d_ij_vec: Vec<RistrettoPoint> = dij_bin.iter().zip(wij_pub.iter()).map(|(dij, wij)| dij * g + wij * h).collect();
            let d_ij_bis_vec: Vec<RistrettoPoint> = d_ij_vec.iter().map(|d_ij| d_ij - g).collect();
            
            d_private_bin_vec.push(dij_bin);
            d_private_vec.push(dij);
            c_vec.push(d_ij_vec);
            c_bis_vec.push(d_ij_bis_vec);
            w.push(wij_pub); // push the wiju list
        }
    }
    return (c_vec, c_bis_vec, w, d_private_bin_vec, d_private_vec) // (D_iju), (D_iju/g), (w_iju), (d_iju), (d_ij)
}

//  M_iu = g ^ MPD_iu * h ^ z_iu
pub fn calculate_mpd_commit<T: CryptoRng + RngCore>(
    g: &RistrettoPoint,
    h: &RistrettoPoint,
    mpd: Vec<Vec<Scalar>>, // (MPDi) encoded in binary
    u: usize,
    rng_proof: &mut T,
) -> (Vec<Vec<RistrettoPoint>>, Vec<Vec<RistrettoPoint>>, Vec<Vec<Scalar>>) {

    let l = mpd.len();

    let mut z_vec: Vec<Vec<Scalar>> = Vec::with_capacity(l); // secret keys of (MPDi)
    let mut m_vec: Vec<Vec<RistrettoPoint>> = Vec::with_capacity(l); // commitments of (MPDi) -> (M_iu)
    let mut m_bis_vec: Vec<Vec<RistrettoPoint>> = Vec::with_capacity(l); // commitments of (MPDi) -> (M_iu/g)

    for i in 0..l {
        let mpd_i = &mpd[i];

        // Random z-values
        let zi_pub: Vec<Scalar> = (0..u).map(|_| random_scalar(rng_proof)).collect();
        z_vec.push(zi_pub.clone());

        // Commitments
        let mut mpd_i_commit: Vec<RistrettoPoint> = Vec::with_capacity(u);
        let mut mpd_i_commit_bis: Vec<RistrettoPoint> = Vec::with_capacity(u);

        for bit in 0..u {
            let m_iu = *g * mpd_i[bit] + *h * zi_pub[bit];
            mpd_i_commit.push(m_iu);

            // m' = m - g
            let m_iu_bis = m_iu - *g;
            mpd_i_commit_bis.push(m_iu_bis);
        }

        m_vec.push(mpd_i_commit);
        m_bis_vec.push(mpd_i_commit_bis);
    }

    (m_vec, m_bis_vec, z_vec)
}