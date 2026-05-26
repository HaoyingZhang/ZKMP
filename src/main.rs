#[allow(unused_imports)]
#[allow(unused_variables)]
use rand_core::OsRng;
use curve25519_dalek::{ scalar::Scalar};

use zkmp::square::*;        
use zkmp::distance::*;  
use zkmp::mpd_bin::*;  
use zkmp::mpd_exist::*;
use zkmp::mpd_min::*;
use zkmp::comp::*;
use zkmp::comp_bis::*;
use zkmp::threshold::*;
use zkmp::scenarios::*;
// use zkmp::threshold_bis::*;
use zkmp::commit::*;
use zkmp::threshold_bis_no_sim::*;
use zkmp::comp_bis_ano::*;
use zkmp::extraction::*;


fn main() {
    println!("Execution in progress...");
    let mut rng = OsRng;
    let mut rng_k = OsRng;
    let mut rng_proof_square = OsRng;

    let n: usize = 1000;
    let upper: usize = 45;
    let u: usize = 20; // u=13, u=15 and u=20
    let m: usize = 100;
    let l = n.checked_sub(m).and_then(|x| x.checked_add(1)).expect("n must be >= m - 1");
    let iter: usize = 1;
    let threshold_anomaly = 210000;
    let threshold_similarity = 50;

    // measure_time_proof_extraction(upper, n, m, iter);

    measure_signature(upper, n, iter);

    // scenarios

    measure_time_comp_no_similarity(upper, n, m, u, iter, threshold_similarity);

    measure_time_comp_anomaly(upper, n, m, u, iter, threshold_similarity);

    measure_time_non_anomaly(upper, n, m, u, iter, threshold_anomaly);
    
    measure_time_similarity(upper, n, m, u, iter, threshold_similarity);

    // unit proofs
    
    measure_time_proof_square(upper,n, m, iter);

    measure_time_proof_distance(upper,n,m,u,iter);

    // measure_time_proof_MPD(upper, n, m, u, iter);

    // measure_time_exist_bin(upper, n, m, u, iter);

    // measure_time_mpd_min(upper, n, m, u, iter);

    measure_time_comp_anomaly(upper, n, m, u, iter, threshold_similarity);

    // no ano
    measure_time_comp(upper, n, m, u, iter, threshold_anomaly);

    // sim
    measure_time_comp_similarity(upper, n, m, u, iter, threshold_anomaly);

    // no sim
    measure_time_comp_no_similarity(upper, n, m, u, iter, threshold_similarity);
    
}