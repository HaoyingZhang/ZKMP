# Artifacts of ZKPMP: Zero-Knowledge Proofs for Subsequence Anomaly and Similarity Detection in Time Series via the Matrix Profile (under review of AsiaCCS 2026)

We propose implementations of 7 unit proofs: square, distance, mpd_bin, mpd_exist, mpd_min, no_sim, and no_ano. The source code of these schemas can be found under ```src/schemas/``` folder.

The commitment phases are coded seperately in ```src/schemas/commit.rs```

To launch the unit tests: ```cargo test --lib```

To launch the execution time measurement: ```cargo run --release``` 
