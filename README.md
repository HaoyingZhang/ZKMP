# Artifacts of ZKPMP: Verifiable Anomaly and Similarity Detection Using Matrix Profile in Private Time-series

To measure the signature time, use function ```measure_signature``` in main.

To measure the time per scenario, modify in main by switching between: 
- measure_time_similarity
- measure_time_non_anomaly
- measure_time_comp_no_similarity
- measure_time_comp_anomaly

We propose implementations of 7 unit proofs: 
- com
- square
- distance_bin
- prove_non_anomaly_i (src/schemas/comp.rs)
- prove_comp_similarity (src/schemas/comp_bis.rs)
- prove_comp_anomaly (src/schemas/comp_bis_ano.rs)
- prove_comp_no_sim (src/schemas/threshold_bis_no_sim.rs)

All the source code of these schemas can be found under ```src/schemas/``` folder.

The commitment phases are coded seperately in ```src/schemas/commit.rs```

To launch the unit tests: ```cargo test --lib```

To launch the execution time measurement: ```cargo run --release``` 
