use curve25519_dalek::{ scalar::Scalar, RistrettoPoint};



// Definition of the structure for the setup set:
#[derive(Clone, Debug, PartialEq)]
pub struct Set { 
    pub gen: RistrettoPoint, //G 
    pub h_: RistrettoPoint, //h
    pub n_: usize //n (length of the time series)
}

// Definition of the structure for the commitment:
#[derive(Clone, Debug, PartialEq)]
pub struct Commit { 
    pub c_: Vec<RistrettoPoint>, // commitment
    pub k_: Vec<Scalar>, // private keys
    pub x_: Vec<Scalar> // time series
}

// Witness for a pair (i,j): (x_ij, k_ij).
pub struct PairWitness {
    pub x_ij: Scalar,  // x_i - x_j
    pub k_ij: Scalar,  // k_i - k_j
}

// The structure of the proof suqare ij
pub struct ProofSquareij{
    pub r_1: RistrettoPoint,
    pub r_2: RistrettoPoint,
    pub s_1: RistrettoPoint,
    pub s_2: RistrettoPoint,
    pub u: Scalar,
    pub v1: Scalar,
    pub v2: Scalar
}

pub struct ProofDistanceiju{
    pub r_1: RistrettoPoint,
    pub r_2: RistrettoPoint,
    pub c_1: Scalar,
    pub c_2: Scalar,
    pub response_1: Scalar,
    pub response_2: Scalar,
}

pub struct ProofMPDBiniu{
    pub r_1: RistrettoPoint,
    pub r_2: RistrettoPoint,
    pub c_1: Scalar,
    pub c_2: Scalar,
    pub response_1: Scalar,
    pub response_2: Scalar,
}

pub struct ProofExistij{
    pub r_i: Vec<RistrettoPoint>,
    pub c_i: Vec<Scalar>,
    pub z_i: Vec<Scalar>
}

pub struct ProofMPDMinOR {
    pub r: Vec<RistrettoPoint>,
    pub c: Vec<Scalar>,
    pub z: Vec<Scalar>
}

pub struct ProofMPDMinAND {
    pub r1: RistrettoPoint,
    pub c: Scalar,
    pub z1: Scalar,
}

pub struct ZKmin{
    pub commitments: Vec<RistrettoPoint>,
    pub challenges: Vec<Scalar>,
    pub responses: Vec<Scalar>,
}

#[derive(Clone)]
pub struct ZKthresholdi{
    pub commitments: Vec<RistrettoPoint>,
    pub challenges: Vec<Scalar>,
    pub responses: Vec<Scalar>
}