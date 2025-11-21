/// Recursive proof construction for
/// π_{MPD_min,i,j} ← NIP{ ... over u ∈ [ℓ] ... }.
///
/// Each level u proves either:
///  - A_u:   g·M_i[u]/D_ij[u] = h^{z_i[u] - w_ij[u]}  (left branch)
///  - B_u:   M_i[u]/D_ij[u] = h^{z_i[u] - w_ij[u]}    (right branch)
///
/// The recursion builds a proof for A_u ∨ (B_u ∧ previous(u-1)).
pub fn proof_mpd_min_ij<R: RngCore + CryptoRng>(
    g: &RistrettoPoint,
    h: &RistrettoPoint,
    u: usize,                // current recursion depth (1..=ℓ)
    zi: &[Scalar],
    wij: &[Scalar],
    m_i: &[RistrettoPoint],
    d_ij: &[RistrettoPoint],
    rng: &mut R,
    challenge: Option<Scalar>,
) -> ProofMPDMinOR {
    assert!(u >= 1, "u must be ≥ 1");
    let idx = u - 1;

    // Elements at level u
    let y1 = *g + m_i[idx] - d_ij[idx]; // corresponds to g*M_i / D_ij
    let y2 = m_i[idx] - d_ij[idx];      // corresponds to M_i / D_ij
    let alpha = zi[idx] - wij[idx];

    if 

    // Helper: left real (A_u), right simulated
    let mut build_left_real = |child: Option<Box<ProofMPDMinAND>>, c_opt: Option<Scalar>| -> ProofMPDMinOR {
        // Simulate right
        let c2 = random_scalar(rng);
        let z2 = random_scalar(rng);
        let r2 = *h * z2 - y2 * c2;

        // Real left
        let r = random_scalar(rng);
        let r1 = *h * r;

        // Node challenge
        let c = c_opt.unwrap_or_else(|| chal_distance(&r1, &r2, h, &y1, &y2));
        let c1 = c - c2;
        let z1 = r + c1 * alpha;

        ProofMPDMinOR { r1, r2, c1, c2, z1, z2, child }
    };

    // Helper: right real (B_u), left simulated
    let mut build_right_real = |child: Option<Box<ProofMPDMinAND>>, c_opt: Option<Scalar>| -> ProofMPDMinOR {
        // Simulate left
        let c1 = random_scalar(rng);
        let z1 = random_scalar(rng);
        let r1 = *h * z1 - y1 * c1;

        // Real right
        let r = random_scalar(rng);
        let r2 = *h * r;

        // Node challenge
        let c = c_opt.unwrap_or_else(|| chal_distance(&r1, &r2, h, &y1, &y2));
        let c2 = c - c1;
        let z2 = r + c2 * alpha;

        ProofMPDMinIJ { r1, r2, c1, c2, z1, z2, child }
    };

    // Decide which branch is true
    let a_true = (*h) * alpha == y1;

    if u == 1 {
        // Base case: no child
        if a_true {
            build_left_real(None, challenge)
        } else {
            build_right_real(None, challenge)
        }
    } else {
        // Recursive: A_u ∨ (B_u ∧ prev(u-1))
        if a_true {
            // Stop here (no child needed)
            build_left_real(None, challenge)
        } else {
            ProofMPDMinOR{}
            // Need child for previous(u-1)
            // If you want the SAME fixed challenge at all levels, pass `challenge` below instead of `None`.
            let child = proof_mpd_min_ij(g, h, u - 1, zi, wij, m_i, d_ij, rng, None);
            build_right_real(Some(Box::new(child)), challenge)
        }
    }
}

pub fn verify_mpd_min_ij<R: RngCore + CryptoRng>(
    g: &RistrettoPoint,
    h: &RistrettoPoint,
    u: usize,                // current recursion depth (1..=ℓ)
    m_i: &[RistrettoPoint],
    d_ij: &[RistrettoPoint],
    proof: ProofMPDMinIJ,
    rng: &mut R,
) -> bool{
    assert!(u >= 1, "u must be ≥ 1");
    let idx = u - 1;

    // Compute the two candidate group elements for this level.
    let y1 = *g + m_i[idx] - d_ij[idx]; // corresponds to "g*M_i / D_ij"
    let y2 = m_i[idx] - d_ij[idx];      // corresponds to "M_i / D_ij"

    let prove_or = |proof: &ProofMPDMinIJ, r1: &RistrettoPoint,r2: &RistrettoPoint,c1: Scalar,c2: Scalar,z1: Scalar,z2: Scalar,took_right_branch: bool ,child: Option<Box<ProofMPDMinIJ>>| -> bool {
        let c = chal_distance(&r1, &r2, &h, &y1, &y2);
        let res_1 = proof[idx].response_1; //R1
        let res_2 = proof[idx].response_2; //R2
        let r1  = proof[idx].r_1; // r
        let r2  = proof[idx].r_2; // r_
        let c1  = proof[idx].c_1; // c1
        let c2  = proof[idx].c_2; // c2

        if (res_1 * h - c1 * y1 != r1) || (res_2 *h - c2 * y2 != r2) || (c != c1 + c2)  {
            return false;
        }
        if took_right_branch && Some(child){
            verify_mpd_min_ij(g, h, u-1, zi, wij, m_i, d_ij, child, rng);
        }
        true
    };

    let prove_and = |proof: &ProofMPDMinIJ, r1: &RistrettoPoint,r2: &RistrettoPoint,c1: Scalar,c2: Scalar,z1: Scalar,z2: Scalar,took_right_branch: bool ,child: Option<Box<ProofMPDMinIJ>>| -> bool {
        let c = chal_distance(&r1, &r2, &h, &y1, &y2);
        ???
    };
    
    
}