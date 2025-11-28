#[allow(unused_imports)]
#[allow(unused_variables)]
use rand_core::OsRng;
use curve25519_dalek::{ scalar::Scalar};

use zkmp::firstlib::*;        // everything public in firstlib
use zkmp::usefulfuncs::*;     // functions like random_scalar, etc.
use zkmp::usefulstructs::*;   // your types

fn main() {
    println!("Execution in progress...");
    let mut rng = OsRng;
    let mut rng_k = OsRng;
    let mut rng_proof_square = OsRng;

    let n: usize = 1000;
    let upper: usize = 256;
    let u: usize = 16;
    // let ts_scalar = random_ecg(&mut rng, n, upper);
    // let mut set: Set = setup(n, &mut rng);
    // let c: Commit = commit(&mut set, &ts_scalar, &mut rng_k); // commit of device
    // let x: &Vec<Scalar> = open(&c);
    // println!("{:?}", x);

    let m: usize = 100;
    let l = n.checked_sub(m).and_then(|x| x.checked_add(1)).expect("n must be >= m - 1");
    let iter: usize = 1;
    let threshold = 20;
    
    // measure_time_proof_square(&ts_scalar,n, m, iter);

    measure_time_proof_distance(upper,n,m,u,iter);

    // measure_time_proof_MPD(&ts_scalar, n, m, u, iter);

    // measure_time_exist_bin(&ts_scalar, n, m, u, iter);

    // measure_time_mpd_min(&ts_scalar, n, m, u, iter);

    // measure_time_non_similarity(&ts_scalar, n, m, u, iter, threshold);
    
}

pub fn measure_time_no_similarity(
    iter: usize,
    n: usize,
    m: usize,
    u: usize,
    iter: usize,
) -> (){
    // RNGs
    let mut rng = OsRng;
    let mut rng_k = OsRng;
    let mut rng_proof = OsRng;

    let mut time_setup              = Duration::ZERO;
    let mut time_commit             = Duration::ZERO;
    let mut time_proof_distance     = Duration::ZERO;
    let mut time_verify_distance    = Duration::ZERO;

    // --- Setup ---
    let t0 = Instant::now();
    let mut set = setup(n, &mut rng);
    time_setup += t0.elapsed();

    for _ in 0..iter {
        let ts = random_ecg(&mut rng, n, upper);

        // --- Commit ---
        let c = commit(&mut set, ts, &mut rng_k);
        
        let g = set.gen;
        let h = set.h_;

        let (c_diff, c_tilde, x_diff, k_diff, k_tilde) = calculate_inner_diff_commit(&c, &set, &mut rng_proof);
        
        
        let (c_vec, c_bis_vec, w) = calculate_dist_commit(&mut rng_proof, n, m, u, g, h, &x_diff, &k_diff, &k_tilde);
        
        let c_vec_refs: Vec<&[RistrettoPoint]> = c_vec.iter().map(|inner| inner.as_slice()).collect();
        let c_bis_vec_refs: Vec<&[RistrettoPoint]> = c_bis_vec.iter().map(|inner| inner.as_slice()).collect();
        let w_refs : Vec<&[Scalar]> = w.iter().map(|inner| inner.as_slice()).collect();

        let t1 = Instant::now();

        
        time_commit += t1.elapsed();
    
    }
}
