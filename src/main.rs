#[allow(unused_imports)]
#[allow(unused_variables)]
use rand_core::OsRng;
use curve25519_dalek::{ scalar::Scalar};

use zkmp::square::*;        
use zkmp::distance::*;  
use zkmp::mpd_bin::*;  
use zkmp::mpd_exist::*;
use zkmp::mpd_min::*;
use zkmp::no_sim::*;
use zkmp::no_ano::*;
use zkmp::usefulfuncs::*;     // functions like random_scalar, etc.
use zkmp::usefulstructs::*;   // your types

fn main() {
    println!("Execution in progress...");
    let mut rng = OsRng;
    let mut rng_k = OsRng;
    let mut rng_proof_square = OsRng;

    let n: usize = 100;
    let upper: usize = 45;
    let u: usize = 15; // u=13, u=15 and u=20
    // let ts_scalar = random_ecg(&mut rng, n, upper);
    // let mut set: Set = setup(n, &mut rng);
    // let c: Commit = commit(&mut set, &ts_scalar, &mut rng_k); // commit of device
    // let x: &Vec<Scalar> = open(&c);
    // println!("{:?}", x);

    let m: usize = 10;
    let l = n.checked_sub(m).and_then(|x| x.checked_add(1)).expect("n must be >= m - 1");
    let iter: usize = 5;
    let threshold = 10;
    
    // measure_time_proof_square(upper,n, m, iter);

    // measure_time_proof_distance(upper,n,m,u,iter);

    // measure_time_proof_MPD(upper, n, m, u, iter);

    // measure_time_exist_bin(upper, n, m, u, iter);

    // measure_time_mpd_min(upper, n, m, u, iter);

    // measure_time_non_similarity(upper, n, m, u, iter, threshold);

    measure_time_non_anomaly(upper, n, m, u, iter, threshold);
    
}