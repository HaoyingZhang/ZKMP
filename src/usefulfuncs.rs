use rand::{ Rng, thread_rng };
use rand_core::{ CryptoRng, RngCore, OsRng, CryptoRngCore };   
use curve25519_dalek::{ scalar::Scalar, RistrettoPoint, traits::Identity, constants::RISTRETTO_BASEPOINT_POINT, constants::RISTRETTO_BASEPOINT_TABLE };
use zeroize::Zeroize; 
use curve25519_dalek::ristretto::CompressedRistretto;
use crate::usefulstructs::*;
use digest::Digest;
use sha2::Sha512;

// Generates a random Scalar:
pub fn random_scalar<T: CryptoRngCore + ?Sized>(rng: &mut T) -> Scalar {
    let mut scalar_bytes = [0u8;64];
    rng.fill_bytes(&mut scalar_bytes);
    let res  = Scalar::from_bytes_mod_order_wide(&scalar_bytes);
    return res;
}

pub fn random_ecg<T: CryptoRngCore + ?Sized>(rng: &mut T, n: usize, upper: usize) -> Vec<Scalar> {
    // Generate random integers in [0, upper] and convert to Scalar
    let scalars: Vec<Scalar> = (0..n)
        .map(|_| {
            let r: u64 = rng.gen_range(0..=(upper as u64));
            Scalar::from(r)
        })
        .collect();

    return scalars;
}

// Generates a vector of random scalar:
pub fn random_vec_scalar<T: CryptoRngCore + ?Sized>(rng: &mut T, n: usize)-> Vec<Scalar>{
    let mut l_scalar:   Vec<Scalar>  = Vec::with_capacity(n);
    for _i in 0..n{
        l_scalar.push(random_scalar(rng));
    }
    return l_scalar;
}

// Generates a random RistrettoPoint element:
pub fn random_ristretto_point<T: CryptoRng + RngCore>(rng: &mut T) -> RistrettoPoint{   
    let r = random_scalar(rng);
    let g = &r*RISTRETTO_BASEPOINT_TABLE; // notation additive
    return g;
}

pub fn generate_ristretto_point(x: Scalar) -> RistrettoPoint{
    let g = &x*RISTRETTO_BASEPOINT_TABLE;
    return g;
}

// Hash a vector of bytes:
pub fn hash(digest: Vec<[u8;32]>) -> Scalar{

    let mut hasher = <Sha512 as Digest>::new();
    for d in digest{
        hasher.update(d.as_slice());
    }
    let result = hasher.finalize();
    Scalar::from_bytes_mod_order_wide(&result.into())
}

pub fn chal_single_proof_square(
    r1: &RistrettoPoint,
    r2: &RistrettoPoint,
    s1: &RistrettoPoint,
    s2: &RistrettoPoint,
    cij: &RistrettoPoint, 
    cij_tilde: &RistrettoPoint, 
    g: &RistrettoPoint, 
    h: &RistrettoPoint
) -> Scalar{
    let mut prehash: Vec<[u8;32]> = Vec::new();  
    prehash.push(*(r1.compress()).as_bytes());
    prehash.push(*(r2.compress()).as_bytes());
    prehash.push(*(s1.compress()).as_bytes());
    prehash.push(*(s2.compress()).as_bytes());
    prehash.push(*(cij.compress()).as_bytes());
    prehash.push(*(cij_tilde.compress()).as_bytes());
    prehash.push(*(g.compress()).as_bytes());
    prehash.push(*(h.compress()).as_bytes());
    prehash.push(*(cij.compress()).as_bytes());
    prehash.push(*(h.compress()).as_bytes());
    return hash(prehash)
}

pub fn chal_distance(
    r1: &RistrettoPoint, 
    r2: &RistrettoPoint, 
    h: &RistrettoPoint, 
    d_iju: &RistrettoPoint,
    d_iju_bis: &RistrettoPoint
)-> Scalar{
    let mut prehash: Vec<[u8;32]> = Vec::new();  
    prehash.push(*(r1.compress()).as_bytes());
    prehash.push(*(r2.compress()).as_bytes());
    prehash.push(*(h.compress()).as_bytes());
    prehash.push(*(h.compress()).as_bytes());
    prehash.push(*(d_iju.compress()).as_bytes());
    prehash.push(*(d_iju_bis.compress()).as_bytes());
    return hash(prehash)
}

pub fn chal_list(
    r: &[RistrettoPoint],
    y: &[RistrettoPoint],
    g: &[RistrettoPoint]
)-> Scalar{
    let mut prehash: Vec<[u8;32]> = Vec::new(); 
    for ri in r{
        prehash.push(*(ri.compress()).as_bytes());
    }
    for yi in y{
        prehash.push(*(yi.compress()).as_bytes());
    }
    for gi in g{
        prehash.push(*(gi.compress()).as_bytes());
    }
    return hash(prehash);
}

pub fn scalar_to_bits(s: &Scalar, u: usize) -> Vec<Scalar> {
    let bytes = s.to_bytes(); // 32 bytes = 256 bits, little-endian

    (0..u)
        .map(|bit| {
            let byte_index = bit / 8;
            let bit_index = bit % 8;
            let bit_is_set = (bytes[byte_index] >> bit_index) & 1 == 1;

            if bit_is_set {
                Scalar::ONE
            } else {
                Scalar::ZERO
            }
        })
        .collect()
}

pub fn convert_bin_to_scalar(bits_lsb_first: &[Scalar]) -> Scalar {
    let mut res  = Scalar::ZERO;
    let mut pow2 = Scalar::ONE;          // = 2^0

    for b in bits_lsb_first {
        // This line *is* res += (2^i) * bits[i], in field arithmetic:
        res += pow2 * *b;

        // advance 2^i -> 2^(i+1) via doubling in the field
        pow2 = pow2 + pow2;
    }
    res
}

/// Helper: 2^i as a Scalar (i >= 0)
pub fn two_pow(i: usize) -> Scalar {
    let two = Scalar::from(2u64);
    // fast exponentiation by repeated squaring
    let mut base = two;
    let mut exp = i;
    let mut acc = Scalar::ONE;
    while exp > 0 {
        if exp & 1 == 1 { acc *= base; }
        base *= base;
        exp >>= 1;
    }
    acc
}

/// Helper: sum_{t=0}^{v.len()-1} v[t] * 2^t
pub fn lincomb_pow2(v: &[Scalar]) -> Scalar {
    v.iter().enumerate().fold(Scalar::ZERO, |acc, (i, s)| acc + (*s) * two_pow(i))
}


// ===================== Function for Matrix Profile ====================
#[inline]
fn scalar_lt(a: &Scalar, b: &Scalar) -> bool {
    let aa = a.to_bytes();
    let bb = b.to_bytes();
    for k in (0..32).rev() {
        if aa[k] != bb[k] {
            return aa[k] < bb[k];
        }
    }
    false // equal
}

/// Squared Euclidean distance between two subsequences (Scalar arithmetic).
#[inline]
fn sq_euclid(ts: &[Scalar], i: usize, j: usize, m: usize) -> Scalar {
    let mut acc = Scalar::ZERO;
    for k in 0..m {
        let d = ts[i + k] - ts[j + k];
        acc += d * d;
    }
    acc
}

/// Compute Matrix Profile (self-join) with window `m` using Scalar arithmetic.
/// Returns a length `w = n - m + 1` vector of **squared** distances as Scalars.
/// Exclusion zone = m/2 (common choice).
pub fn compute_mpd_with_window_scalar(ts: &[Scalar], m: usize) -> Vec<Scalar> {
    let n = ts.len();
    assert!(m >= 2, "window m must be >= 2");
    assert!(m <= n, "window m must be <= n");

    let w  = n - m + 1;
    let ez = m / 2;

    let mut profile = Vec::with_capacity(w);

    for i in 0..w {
        // 1) Find the first valid neighbor to seed `best`
        let mut best: Option<Scalar> = None;
        for j in 0..w {
            if i.abs_diff(j) > ez {
                best = Some(sq_euclid(ts, i, j, m));
                break;
            }
        }

        // 2) If no valid neighbor exists, define MPD[i] = 0
        if best.is_none() {
            profile.push(Scalar::ZERO);
            continue;
        }

        // 3) Scan all valid neighbors and take the minimum
        let mut best_val = best.unwrap();
        for j in 0..w {
            if i.abs_diff(j) <= ez { continue; }
            let d2 = sq_euclid(ts, i, j, m);
            if scalar_lt(&d2, &best_val) {
                best_val = d2;
            }
        }

        profile.push(best_val);
    }

    profile
}
