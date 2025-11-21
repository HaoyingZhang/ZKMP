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

    let n: usize = 100;
    let upper: usize = 256;
    let u: usize = 16;
    let ts_scalar = random_ecg(&mut rng, n, upper);
    let mut set: Set = setup(n, &mut rng);
    let c: Commit = commit(&mut set, &ts_scalar, &mut rng_k); // commit of device
    let x: &Vec<Scalar> = open(&c);

    let m: usize = 10;
    let l = n.checked_sub(m).and_then(|x| x.checked_add(1)).expect("n must be >= m - 1");
    let iter: usize = 10;
    
    // measure_time_proof_square(&ts_scalar,n, m, iter);

    measure_time_proof_distance(&ts_scalar,n,m,u,iter);

    // measure_time_proof_MPD(&ts_scalar, n, m, u, iter);

    // measure_time_exist_bin(&ts_scalar, n, m, u, iter);

    // measure_time_mpd_min(&ts_scalar, n, m, u, iter);
    
}
