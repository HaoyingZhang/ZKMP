use curve25519_dalek::{ scalar::Scalar, RistrettoPoint, traits::Identity};
use rand_core::{ OsRng, CryptoRng, RngCore, CryptoRngCore };   
use std::time::{ Instant, Duration }; 

use crate::square::*;        
use crate::distance::*;  
use crate::mpd_bin::*;  
use crate::mpd_exist::*;
use crate::mpd_min::*;
use crate::threshold::*;
use crate::comp::*;
use crate::commit::*;
use crate::comp_bis::*;
use crate::usefulfuncs::*;     // functions like random_scalar, etc.
use crate::usefulstructs::*;   // your types

// pub fn measure_time_non_similarity(
//     upper: usize,
//     n: usize,   // length of time series
//     m: usize,   // window size
//     u: usize, // number of bits (ℓ)
//     iter: usize,
//     epsilon: u64
// ) {
//     let a = n - m + 1; // number of MPD entries (indices i ∈ I

//     let mut time_setup      = Duration::ZERO;
//     let mut time_commit     = Duration::ZERO;

//     let mut time_proof_square     = Duration::ZERO;
//     let mut time_verify_square    = Duration::ZERO;

//     let mut time_proof_distance   = Duration::ZERO;
//     let mut time_verify_distance  = Duration::ZERO;

//     let mut time_proof_mpd_bin    = Duration::ZERO;
//     let mut time_verify_mpd_bin   = Duration::ZERO;

//     let mut time_proof_mpd_exist  = Duration::ZERO;
//     let mut time_verify_mpd_exist = Duration::ZERO;

//     let mut time_proof_mpd_min    = Duration::ZERO;
//     let mut time_verify_mpd_min   = Duration::ZERO;

//     let mut time_proof_threshold  = Duration::ZERO;
//     let mut time_verify_threshold = Duration::ZERO;

//     for _ in 0..iter {
//         let mut rng       = OsRng;
//         let mut rng_k     = OsRng;
//         let mut rng_proof = OsRng;

//         // --- 1) Initialize TS and MPD and threshold -------------------------------
//         let ts = random_ecg(&mut rng, n, upper);
//         let mpd = compute_mpd_with_window_scalar(&ts, m); // length a
//         // println!("{:?}", mpd);
//         // Binary decomposition MPD_i -> {MPD_{i,u}}_{u=0..u-1}
//         let mpd_bin: Vec<Vec<Scalar>> = mpd
//             .iter()
//             .map(|val| scalar_to_bits(val, u)) // each is length u, bits 0/1 as Scalar
//             .collect();
            
//         let epsilon_bin_val = scalar_to_bits(&Scalar::from(epsilon), u);
//         let mut epsilon_bin : Vec<usize> = Vec::with_capacity(u);
//         for bit in 0..epsilon_bin_val.len(){
//             if epsilon_bin_val[bit] == Scalar::ONE{
//                 epsilon_bin.push(bit);
//             }
//         }

//         // --- 2) Setup ----------------------------------------------------
//         let t0 = Instant::now();
//         let mut set = setup(n, &mut rng);
//         time_setup += t0.elapsed();

//         let g = set.gen;
//         let h = set.h_;

//         // --- 3) Commit original time series --------
//         let t1 = Instant::now();
//         let commitment = commit(&mut set, &ts.to_vec(), &mut rng_k);

//         // --- 4) Commit square --------
//         let (c_diff, c_tilde, x_diff, k_diff, k_tilde) = calculate_inner_diff_commit(&commitment, &set, &mut rng);
//         let duration_commit_square = t1.elapsed();
//         time_commit += duration_commit_square;
//         println!("Commit square : {:?}", duration_commit_square);

//         // --- 5) Proof Square -----
//         let start_proof_square = Instant::now();
//         let p_square = proof_square(&commitment, &set, n, m, &x_diff, &k_diff, &c_diff, &c_tilde, &k_tilde, &mut rng_k);

//         let duration_proof_square = start_proof_square.elapsed();
//         time_proof_square += duration_proof_square;
//         println!("Square proof: {:?}", duration_proof_square);
        
//         // --- 6) Vefify Square -----
//         let start_verify_square = Instant::now();
//         let res = verify_square(n, &c_diff, &c_tilde, &set, &p_square);
//         let duration_verify_square = start_verify_square.elapsed();
//         time_verify_square += duration_verify_square;
//         println!("Square verify: {:?}", duration_verify_square);
//         println!("==== Verify for Square: {} ====", res);
//         debug_assert!(res, "square proof failed verification"); 

//         // --- 7) Commit Distance -----
//         let start_commit_distance = Instant::now();
//         let (c_vec, c_bis_vec, w, d_private_vec, _) = calculate_dist_commit(&mut rng_proof, n, m, u, g, h, &x_diff, &k_diff, &k_tilde);
        
//         let c_vec_refs: Vec<&[RistrettoPoint]> = c_vec.iter().map(|inner| inner.as_slice()).collect();
//         let c_bis_vec_refs: Vec<&[RistrettoPoint]> = c_bis_vec.iter().map(|inner| inner.as_slice()).collect();
//         let w_refs : Vec<&[Scalar]> = w.iter().map(|inner| inner.as_slice()).collect();
//         let d_private_refs : Vec<&[Scalar]> = d_private_vec.iter().map(|inner| inner.as_slice()).collect();
        
//         let duration_commit_distance = start_commit_distance.elapsed();
//         time_commit += duration_commit_distance;
//         println!("Commit distance : {:?}", duration_commit_distance);

//         // --- 8) Proof Distance -----
//         let t2 = Instant::now();
//         let proofs_owned = proof_distance(n, m, u, &set, &c_vec_refs, &c_bis_vec_refs, &w_refs, &mut rng_proof);
//         let duration_proof_distance = t2.elapsed();
//         time_proof_distance += duration_proof_distance;
//         println!("Proof distance : {:?}", duration_proof_distance);

//         // Convert owned Vec<Option<Vec<_>>> -> borrowed Vec<Option<&[_]>>
//         let proofs_borrowed: Vec<&[ProofDistanceiju]> = proofs_owned.iter().map(|opt| opt.as_slice()).collect();

//         // --- 9) Verify (distance) ---
//         let t3 = Instant::now();
//         let ok = verify_distance(&c_vec_refs, &c_bis_vec_refs, n, m, &set, &proofs_borrowed);
//         let duration_verify_distance = t3.elapsed();
//         time_verify_distance += duration_verify_distance;
//         println!("Verify distance : {:?}", duration_verify_distance);

//         // sanity check
//         println!("Distance verify: {:?}", duration_verify_distance);
//         println!("==== Verify for Distance: {} ====", ok);
//         debug_assert!(ok, "distance proof failed verification");

//         // --- 10) Commit MPD --------
//         let t4 = Instant::now();
//         let (m_vec, m_bis_vec, z_vec) = calculate_mpd_commit(&g, &h, mpd_bin.clone(), u, &mut rng_proof);

//         let m_vec_refs: Vec<&[RistrettoPoint]> = m_vec.iter().map(|inner| inner.as_slice()).collect();
//         let z_vec_refs: Vec<&[Scalar]> = z_vec.iter().map(|inner| inner.as_slice()).collect();

//         let duration_commit_mpd = t4.elapsed();
//         time_commit += duration_commit_mpd;
//         println!("Commit MPD : {:?}", duration_commit_mpd);

//         // --- 11) Proof MPD --------
//         let t2 = Instant::now();
//         let proofs_owned = proof_MPD_bin(&m_vec, &m_bis_vec, &z_vec, n, m, u, &h, &mut rng_proof);
//         let duration_proof_mpd = t2.elapsed();
//         time_proof_mpd_bin += duration_proof_mpd;
//         println!("MPD bin Proof: {:?}", duration_proof_mpd);

//         // --- 10) Verify MPD --------
//         let t3 = Instant::now();
//         let ok = verify_MPD_bin(n, m, &m_vec, &set, &proofs_owned);
//         let duration_verify_mpd = t3.elapsed();
//         time_verify_mpd_bin += duration_verify_mpd;
//         println!("MPD bin Verify : {:?}", duration_verify_mpd);

//         println!("==== Verify for MPD bin : {} ====", ok);
//         debug_assert!(ok, "MPD bit proof failed verification");

//         // --- 10) Proof MPD exist + Verify --------
//         let mut time_proof_iter  = Duration::ZERO;
//         let mut time_verify_iter = Duration::ZERO;
//         let mut res = true;
//         for i in 0..a{
//             let m_i = m_vec_refs[i];
//             let d_ij = &c_vec_refs[i*a .. i*a + a];
//             let zi_pub = z_vec_refs[i];
//             let w_ij = &w_refs[i*a .. i*a+a];

//             let t_proof = Instant::now();
//             let proof_existence = proof_exist_bin(&set, u, a, &m_i, d_ij, &zi_pub, w_ij, &mut rng_proof);
//             time_proof_iter += t_proof.elapsed();

//             // --- Verify ---
//             let t_verify = Instant::now();
//             res &= verify_exist_bin(&m_i, d_ij, u, a, &set, &proof_existence);
//             time_verify_iter += t_verify.elapsed(); 
//         }
//         println!("MPD Exist Proof {:?} :", {time_proof_iter});
//         println!("MPD Exist Verify {:?} :", {time_verify_iter});
//         time_proof_mpd_exist += time_proof_iter;
//         time_verify_mpd_exist += time_verify_iter;

//         println!("==== Verify for MPD exist : {} ====", res);
//         debug_assert!(res, "verify_exist_bin failed");

//         // --- 10) Proof MPD min --------
//         let mut alpha_list : Vec<Vec<Scalar>> = Vec::with_capacity(a*a);
//         let mut y_list : Vec<Vec<RistrettoPoint>> = Vec::with_capacity(a*a);

//         for i in 0..a{
//             for j in 0..a{
//                 let mut alpha_buffer : Vec<Scalar> = Vec::with_capacity(2*u);
//                 let mut y_buffer : Vec<RistrettoPoint> = Vec::with_capacity(2*u);
//                 for bit in 0..u{
//                     let alpha_i_ell_ = z_vec_refs[i][bit] - w_refs[i*a+j][bit];
//                     alpha_buffer.push(alpha_i_ell_);
//                     alpha_buffer.push(alpha_i_ell_);
//                     let y_buffer_pair_ = m_vec_refs[i][bit] - c_vec_refs[i*a+j][bit];
//                     let y_buffer_impair_ = m_vec_refs[i][bit] - c_vec_refs[i*a+j][bit] + g;
//                     y_buffer.push(y_buffer_pair_);
//                     y_buffer.push(y_buffer_impair_);
//                 }
//                 alpha_list.push(alpha_buffer.clone());
//                 y_list.push(y_buffer.clone());
//             }
//         }

//         let y_list_refs: Vec<&[RistrettoPoint]> = y_list.iter().map(|inner| inner.as_slice()).collect();
//         let alpha_list_refs : Vec<&[Scalar]> = alpha_list.iter().map(|inner| inner.as_slice()).collect();

//         let is_real_relation = vec![false; 2 * u];

//         let t_proof = Instant::now();
//         let proof_list = proof_mpd_min(mpd_bin.clone(), &d_private_refs, &h, a, u, m, &alpha_list_refs, &y_list_refs, &mut rng_proof, &is_real_relation);
//         let duration_proof_mpd_min = t_proof.elapsed();
//         time_proof_mpd_min += duration_proof_mpd_min;
//         println!("proof MPD Min :   {:?}", duration_proof_mpd_min);

//         // --- 11) Verify MPD min --------
//         let t_verify = Instant::now();
//         let ok = verify_mpd_min(&h, a, m, &y_list, &mut rng_proof, &proof_list);
//         let duration_verify_mpd_exist = t_verify.elapsed();
//         time_verify_mpd_min += duration_verify_mpd_exist;
//         println!("verify MPD Min :  {:?}", duration_verify_mpd_exist);

//         println!("==== Verify for MPD Min : {} ====", ok);
//         debug_assert!(ok, "verify_mpd_min failed!");

//         // --- 12) Proof threshold time --------------

//         let t_proof = Instant::now();
//         let proof_list = prove_threshold(&mut rng_k, &m_bis_vec, h, &z_vec, &epsilon_bin);
//         let duration_proof_threshold = t_proof.elapsed();
//         time_proof_threshold += duration_proof_threshold;
//         println!("Proof Threshold :   {:?}", duration_proof_threshold);


//         // --- 7) Verify threshold time ---------------
//         let t_verify = Instant::now();
//         let ok = verify_threshold(&h, &m_bis_vec, &proof_list, &epsilon_bin);
//         let duration_verify_threshold = t_verify.elapsed();
//         time_verify_threshold += duration_verify_threshold;
//         println!("Verify Threshold:  {:?}", duration_verify_threshold);

//         println!("==== Verify for Threshold : {} ====", ok);
//         debug_assert!(ok, "verify_threshold failed!");
//     }

//     println!("==== Timing over {} iterations ====", iter);
//     println!("  setup:         {:?}", time_setup/(iter as u32));
//     println!("  commit:        {:?}", time_commit/(iter as u32));
//     println!("  proof (square):   {:?}", time_proof_square/(iter as u32));
//     println!("  verify (square):  {:?}", time_verify_square/(iter as u32));
//     println!("  proof (distance):   {:?}", time_proof_distance/(iter as u32));
//     println!("  verify (distance):  {:?}", time_verify_distance/(iter as u32));
//     println!("  proof (mpd bin):   {:?}", time_proof_mpd_bin/(iter as u32));
//     println!("  verify (mpd bin):  {:?}", time_verify_mpd_bin/(iter as u32));
//     println!("  proof (mpd exist):   {:?}", time_proof_mpd_exist/(iter as u32));
//     println!("  verify (mpd exist):  {:?}", time_verify_mpd_exist/(iter as u32));
//     println!("  proof (mpd min):   {:?}", time_proof_mpd_min/(iter as u32));
//     println!("  verify (mpd min):  {:?}", time_verify_mpd_min/(iter as u32));
//     println!("  proof (Threshold):   {:?}", time_proof_threshold/(iter as u32));
//     println!("  verify (Threshold):  {:?}", time_verify_threshold/(iter as u32));
// }

pub fn measure_time_non_anomaly(
    upper: usize,
    n: usize,   // length of time series
    m: usize,   // window size
    u: usize, // number of bits (ℓ)
    iter: usize,
    epsilon: u64
) {
    let a = n - m + 1; // number of MPD entries (indices i ∈ I

    let mut time_setup      = Duration::ZERO;
    let mut time_commit     = Duration::ZERO;

    let mut time_proof_square     = Duration::ZERO;
    let mut time_verify_square    = Duration::ZERO;

    let mut time_proof_distance   = Duration::ZERO;
    let mut time_verify_distance  = Duration::ZERO;

    let mut time_proof_threshold  = Duration::ZERO;
    let mut time_verify_threshold = Duration::ZERO;

    for _ in 0..iter {
        let mut rng       = OsRng;
        let mut rng_k     = OsRng;
        let mut rng_proof = OsRng;

        // --- 1) Initialize TS and MPD and threshold -------------------------------
        let ts = random_ecg(&mut rng, n, upper);
        let mpd = compute_mpd_with_window_scalar(&ts, m); // length a
        // println!("{:?}", mpd);
        // Binary decomposition MPD_i -> {MPD_{i,u}}_{u=0..u-1}
        let mpd_bin: Vec<Vec<Scalar>> = mpd
            .iter()
            .map(|val| scalar_to_bits(val, u)) // each is length u, bits 0/1 as Scalar
            .collect();
            
        let epsilon_bin_val = scalar_to_bits(&Scalar::from(epsilon), u);
        let epsilon_scalar = Scalar::from(epsilon);
        let mut epsilon_bin : Vec<usize> = Vec::with_capacity(u);
        for bit in 0..epsilon_bin_val.len(){
            if epsilon_bin_val[bit] == Scalar::ZERO{
                epsilon_bin.push(bit);
            }
        }

        // --- 2) Setup ----------------------------------------------------
        let t0 = Instant::now();
        let mut set = setup(n, &mut rng);
        time_setup += t0.elapsed();

        let g = set.gen;
        let h = set.h_;

        // --- 3) Commit original time series --------
        let t1 = Instant::now();
        let commitment = commit(&mut set, &ts.to_vec(), &mut rng_k);

        // --- 4) Commit square --------
        let (c_diff, c_tilde, x_diff, k_diff, k_tilde) = calculate_inner_diff_commit(&commitment, &set, &mut rng);
        let duration_commit_square = t1.elapsed();
        time_commit += duration_commit_square;
        println!("Commit square : {:?}", duration_commit_square);

        // --- 5) Proof Square -----
        let start_proof_square = Instant::now();
        let p_square = proof_square(&commitment, &set, n, m, &x_diff, &k_diff, &c_diff, &c_tilde, &k_tilde, &mut rng_k);

        let duration_proof_square = start_proof_square.elapsed();
        time_proof_square += duration_proof_square;
        println!("Square proof: {:?}", duration_proof_square);
        
        // --- 6) Vefify Square -----
        let start_verify_square = Instant::now();
        let res = verify_square(n, &c_diff, &c_tilde, &set, &p_square);
        let duration_verify_square = start_verify_square.elapsed();
        time_verify_square += duration_verify_square;
        println!("Square verify: {:?}", duration_verify_square);
        println!("==== Verify for Square: {} ====", res);
        debug_assert!(res, "square proof failed verification"); 

        // --- 7) Commit Distance -----
        let start_commit_distance = Instant::now();
        let (c_vec, c_bis_vec, w, _, d_private_vec) = calculate_dist_commit(&mut rng_proof, n, m, u, g, h, &x_diff, &k_diff, &k_tilde);
        
        let c_vec_refs: Vec<&[RistrettoPoint]> = c_vec.iter().map(|inner| inner.as_slice()).collect();
        let c_bis_vec_refs: Vec<&[RistrettoPoint]> = c_bis_vec.iter().map(|inner| inner.as_slice()).collect();
        let w_refs : Vec<&[Scalar]> = w.iter().map(|inner| inner.as_slice()).collect();
        
        let duration_commit_distance = start_commit_distance.elapsed();
        time_commit += duration_commit_distance;
        println!("Commit distance : {:?}", duration_commit_distance);

        // --- 8) Proof Distance -----
        let t2 = Instant::now();
        let proofs_owned = proof_distance(n, m, u, &set, &c_vec_refs, &c_bis_vec_refs, &w_refs, &mut rng_proof);
        let duration_proof_distance = t2.elapsed();
        time_proof_distance += duration_proof_distance;
        println!("Proof distance : {:?}", duration_proof_distance);

        // Convert owned Vec<Option<Vec<_>>> -> borrowed Vec<Option<&[_]>>
        let proofs_borrowed: Vec<&[ProofDistanceiju]> = proofs_owned.iter().map(|opt| opt.as_slice()).collect();

        // --- 9) Verify (distance) ---
        let t3 = Instant::now();
        let ok = verify_distance(&c_vec_refs, &c_bis_vec_refs, n, m, &set, &proofs_borrowed);
        let duration_verify_distance = t3.elapsed();
        time_verify_distance += duration_verify_distance;
        println!("Verify distance : {:?}", duration_verify_distance);

        // sanity check
        println!("Distance verify: {:?}", duration_verify_distance);
        println!("==== Verify for Distance: {} ====", ok);
        debug_assert!(ok, "distance proof failed verification");

        // --- 12) Proof threshold time --------------
        let mut time_proof_non_anomaly = Duration::ZERO;
        let mut time_verify_non_anomaly = Duration::ZERO;

        let mut verify_non_anomaly : bool = true;
        let mut t2 : Instant;
        let mut t3 : Instant;
        let half_m = m / 2;

        for i in 0..a{
            // println!("==== i = {} ==== ", i);
            let mut d_i_refs: Vec<&[RistrettoPoint]> = Vec::new();
            let mut w_i_refs: Vec<&[Scalar]> = Vec::new();
            let mut d_private_i_refs : Vec<Scalar> = Vec::new();

            let left_end = i.saturating_sub(half_m);
            let right_start = (i+half_m+1).min(a);
            for j in (0..left_end).chain((right_start..a)) {
                d_i_refs.push(c_vec_refs[i * a + j]);
                w_i_refs.push(w_refs[i * a + j]);
                d_private_i_refs.push(d_private_vec[i * a + j]);
            }

            t2 = Instant::now();
            let proof_i = prove_non_anomaly_i(epsilon, &d_private_i_refs, &epsilon_bin, &d_i_refs, &w_i_refs, h, &mut rng_proof);
            time_proof_non_anomaly += t2.elapsed();

            t3 = Instant::now();
            let res = verify_non_anomaly_i(proof_i, &epsilon_bin, &d_i_refs, h);
            verify_non_anomaly &= res;
            time_verify_non_anomaly += t3.elapsed();
        }
        println! ("Proof Threshold : {:?}", time_proof_non_anomaly);
        println! ("Verify Threshold : {:?}", time_verify_non_anomaly);
        println!("==== Verify for Threshold : {} ==== ", verify_non_anomaly);
        time_proof_threshold += time_proof_non_anomaly;
        time_verify_threshold += time_verify_non_anomaly;
    }

    println!("==== Timing over {} iterations ====", iter);
    println!("  setup:         {:?}", time_setup/(iter as u32));
    println!("  commit:        {:?}", time_commit/(iter as u32));
    println!("  proof (square):   {:?}", time_proof_square/(iter as u32));
    println!("  verify (square):  {:?}", time_verify_square/(iter as u32));
    println!("  proof (distance):   {:?}", time_proof_distance/(iter as u32));
    println!("  verify (distance):  {:?}", time_verify_distance/(iter as u32));
    println!("  proof (Threshold):   {:?}", time_proof_threshold/(iter as u32));
    println!("  verify (Threshold):  {:?}", time_verify_threshold/(iter as u32));
}


pub fn measure_time_similarity(
    upper: usize,
    n: usize,   // length of time series
    m: usize,   // window size
    u: usize, // number of bits (ℓ)
    iter: usize,
    epsilon: u64
) {
    let a = n - m + 1; // number of MPD entries (indices i ∈ I

    let mut time_setup      = Duration::ZERO;
    let mut time_commit     = Duration::ZERO;

    let mut time_proof_square     = Duration::ZERO;
    let mut time_verify_square    = Duration::ZERO;

    let mut time_proof_distance   = Duration::ZERO;
    let mut time_verify_distance  = Duration::ZERO;

    let mut time_proof_threshold  = Duration::ZERO;
    let mut time_verify_threshold = Duration::ZERO;

    for _ in 0..iter {
        let mut rng       = OsRng;
        let mut rng_k     = OsRng;
        let mut rng_proof = OsRng;

        // --- 1) Initialize TS and MPD and threshold -------------------------------
        let ts = random_ecg(&mut rng, n, upper);
        // println!("{:?}", ts);

        let threshold : Scalar = Scalar::from(epsilon);

        // --- 2) Setup ----------------------------------------------------
        let t0 = Instant::now();
        let mut set = setup(n, &mut rng);
        time_setup += t0.elapsed();

        let g = set.gen;
        let h = set.h_;

        // --- 3) Commit original time series --------
        let t1 = Instant::now();
        let commitment = commit(&mut set, &ts.to_vec(), &mut rng_k);

        // --- 4) Commit square --------
        let (c_diff, c_tilde, x_diff, k_diff, k_tilde) = calculate_inner_diff_commit(&commitment, &set, &mut rng);
        let duration_commit_square = t1.elapsed();
        time_commit += duration_commit_square;
        println!("Commit square : {:?}", duration_commit_square);

        // --- 5) Proof Square -----
        let start_proof_square = Instant::now();
        let p_square = proof_square(&commitment, &set, n, m, &x_diff, &k_diff, &c_diff, &c_tilde, &k_tilde, &mut rng_k);

        let duration_proof_square = start_proof_square.elapsed();
        time_proof_square += duration_proof_square;
        println!("Square proof: {:?}", duration_proof_square);
        
        // --- 6) Vefify Square -----
        let start_verify_square = Instant::now();
        let res = verify_square(n, &c_diff, &c_tilde, &set, &p_square);
        let duration_verify_square = start_verify_square.elapsed();
        time_verify_square += duration_verify_square;
        println!("Square verify: {:?}", duration_verify_square);
        println!("==== Verify for Square: {} ====", res);
        debug_assert!(res, "square proof failed verification"); 

        // --- 7) Commit Distance -----
        let start_commit_distance = Instant::now();
        let (c_vec, c_bis_vec, w, d_private_bin_vec, d_private_vec) = calculate_dist_commit(&mut rng_proof, n, m, u, g, h, &x_diff, &k_diff, &k_tilde);
        
        let c_vec_refs: Vec<&[RistrettoPoint]> = c_vec.iter().map(|inner| inner.as_slice()).collect();
        let c_bis_vec_refs: Vec<&[RistrettoPoint]> = c_bis_vec.iter().map(|inner| inner.as_slice()).collect();
        let w_refs : Vec<&[Scalar]> = w.iter().map(|inner| inner.as_slice()).collect();
        let d_private_bin_refs : Vec<&[Scalar]> = d_private_bin_vec.iter().map(|inner| inner.as_slice()).collect();
        
        let duration_commit_distance = start_commit_distance.elapsed();
        time_commit += duration_commit_distance;
        println!("Commit distance : {:?}", duration_commit_distance);

        // --- 8) Proof Distance -----
        let t2 = Instant::now();
        let proofs_owned = proof_distance(n, m, u, &set, &c_vec_refs, &c_bis_vec_refs, &w_refs, &mut rng_proof);
        let duration_proof_distance = t2.elapsed();
        time_proof_distance += duration_proof_distance;
        println!("Proof distance : {:?}", duration_proof_distance);

        // Convert owned Vec<Option<Vec<_>>> -> borrowed Vec<Option<&[_]>>
        let proofs_borrowed: Vec<&[ProofDistanceiju]> = proofs_owned.iter().map(|opt| opt.as_slice()).collect();

        // --- 9) Verify (distance) ---
        let t3 = Instant::now();
        let ok = verify_distance(&c_vec_refs, &c_bis_vec_refs, n, m, &set, &proofs_borrowed);
        let duration_verify_distance = t3.elapsed();
        time_verify_distance += duration_verify_distance;
        println!("Verify distance : {:?}", duration_verify_distance);

        // sanity check
        println!("Distance verify: {:?}", duration_verify_distance);
        println!("==== Verify for Distance: {} ====", ok);
        debug_assert!(ok, "distance proof failed verification");

        // --- 12) Proof threshold time --------------

        let t2 = Instant::now();
        let proofs = prove_comp_similarity(threshold, d_private_vec, n, m, u, &c_vec_refs, &w_refs, h, &mut rng_proof);
        let duration_proof_threshold = t2.elapsed();
        time_proof_threshold += duration_proof_threshold;
        println! ("Proof Threshold : {:?}", duration_proof_threshold);

        let t3 = Instant::now();
        let res = verify_similarity(n, m, u, &proofs, &c_vec_refs, h, threshold);
        let duration_verify_threshold = t3.elapsed();
        time_verify_threshold += duration_verify_threshold; 
        println! ("Verify Threshold : {:?}", duration_verify_threshold);

        println!("==== Verify for Threshold : {} ==== ", res);
    }

    println!("==== Timing over {} iterations ====", iter);
    println!("  setup:         {:?}", time_setup/(iter as u32));
    println!("  commit:        {:?}", time_commit/(iter as u32));
    println!("  proof (square):   {:?}", time_proof_square/(iter as u32));
    println!("  verify (square):  {:?}", time_verify_square/(iter as u32));
    println!("  proof (distance):   {:?}", time_proof_distance/(iter as u32));
    println!("  verify (distance):  {:?}", time_verify_distance/(iter as u32));
    println!("  proof (Threshold):   {:?}", time_proof_threshold/(iter as u32));
    println!("  verify (Threshold):  {:?}", time_verify_threshold/(iter as u32));
}
