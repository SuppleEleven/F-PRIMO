use ark_bn254::{Bn254, Fr as ScalarField, G1Projective as G1, G2Projective as G2};
use ark_ec::{pairing::Pairing, pairing::PairingOutput, AffineRepr, CurveGroup, Group};
use ark_ff::{Field, PrimeField};
use ark_poly::{univariate::DensePolynomial, Polynomial};
use ark_std::{rand::Rng, UniformRand, Zero};
use sha2::{Digest, Sha256};
use std::time::{SystemTime, Duration, Instant};
use std::cell::RefCell;
use std::sync::Mutex;
use lazy_static::lazy_static;
use std::collections::HashSet;

pub type Fr = ScalarField; 
pub type G1Affine = <Bn254 as Pairing>::G1Affine;  
pub type G2Affine = <Bn254 as Pairing>::G2Affine; 
pub type GT = PairingOutput<Bn254>; 

// Structured Reference String (SRS) definition
#[derive(Clone, Debug)]
pub struct SRS {
    pub g1: Vec<G1Affine>,  // Generator vector over G1 group
    pub g2: Vec<G2Affine>,  // Generator vector over G2 group
    pub degree: usize,      // Maximum polynomial degree supported by the SRS
}

// Generate a random scalar
pub fn random_scalar<R: Rng>(rng: &mut R) -> Fr {
    Fr::rand(rng)
}

// Split a vector into first n elements and remaining elements
fn split_vector<T>(vec: &[T], n: usize) -> (&[T], &[T]) {
    vec.split_at(n)
}

// Hash input bytes to a scalar field element
pub fn hash_to_scalar(input: &[u8]) -> Fr {
    let mut hasher = Sha256::new();  // Create SHA256 hasher
    hasher.update(input);            // Update hash state
    let result = hasher.finalize();  // Get hash digest
    Fr::from_le_bytes_mod_order(&result)  // Convert digest to scalar
}

// Compute inner product of two vectors
pub fn inner_product(a: &[Fr], b: &[Fr]) -> Fr {
    assert_eq!(a.len(), b.len());  // Ensure vectors have equal length
    a.iter()
        .zip(b.iter())
        .map(|(x, y)| *x * *y)  // Multiply elements pairwise
        .sum()  // Sum to get inner product
}

/// Embed weight vector as polynomial coefficients
/// Returns coeffs where coeffs[N+1+i] = w[i], all others are zero
pub fn embed_weights_as_poly_coeffs(N: usize, w: &[Fr]) -> Vec<Fr> {
    let mut coeffs = vec![Fr::zero(); N + 1 + w.len()];
    for (i, wi) in w.iter().enumerate() {
        coeffs[N + 1 + i] = *wi;
    }
    coeffs
}

/// Pair a G1 element to GT group
pub fn pair_g1_to_gt(g1: &G1, g2_base: &G2Affine) -> GT {
    Bn254::pairing(g1.into_affine(), *g2_base)
}

/// Scalar multiplication for GT elements (x^i·[T_i]_T in the paper)
pub fn scalar_mul_gt(scalar: Fr, gt_element: GT) -> GT {
    let _ = scalar; // Temporary implementation: implement GT scalar mul/pow as needed
    gt_element
}

#[derive(Clone, Debug)]
pub struct MultiVectorMapping {
    /// Selection mapping for each vector: M[q][i] = index of i-th selected element in q-th vector
    pub mappings: Vec<Vec<usize>>,
    /// Length of each original vector
    pub vector_lengths: Vec<usize>,
}

impl MultiVectorMapping {
    /// Compute s(q) = sum_{i=1}^{q-1} m_i
    pub fn s(&self, q: usize) -> usize {
        self.mappings[..q].iter().map(|v| v.len()).sum()
    }
    
    /// Total number of selected elements across all vectors
    pub fn total_selected(&self) -> usize {
        self.mappings.iter().map(|v| v.len()).sum()
    }
    
    /// Get number of selected elements m_q for q-th vector
    pub fn m_q(&self, q: usize) -> usize {
        self.mappings[q].len()
    }
    
    /// Get M(q, i): index of i-th selected element in q-th vector
    pub fn get(&self, q: usize, i: usize) -> usize {
        self.mappings[q][i]
    }
    
    /// Flatten 2D mapping to 1D (for backward compatibility)
    pub fn flatten(&self) -> Vec<usize> {
        self.mappings.iter().flatten().cloned().collect()
    }
}

lazy_static! {
    static ref EXCLUDED_TIME: Mutex<Duration> = Mutex::new(Duration::new(0, 0));
    static ref EXCLUDED_MODULES: Mutex<HashSet<String>> = Mutex::new(HashSet::new());
}

/// Start timer for operations to exclude from performance measurement
pub fn start_exclude_timer() -> Instant {
    Instant::now()
}
 
/// Stop exclusion timer and add elapsed time to excluded total
pub fn stop_exclude_timer(start_time: Instant) {
    let elapsed = start_time.elapsed();
    if let Ok(mut excluded_time) = EXCLUDED_TIME.lock() {
        *excluded_time += elapsed;
    }
}
 
/// Get total excluded time for performance measurements
pub fn get_excluded_time() -> Duration {
    EXCLUDED_TIME.lock().unwrap().clone()
}

/// Reset the excluded time counter to zero
pub fn reset_excluded_time() {
    if let Ok(mut excluded_time) = EXCLUDED_TIME.lock() {
        *excluded_time = Duration::new(0, 0);
    }
}