use crate::utils::*;
use ark_poly::{univariate::DensePolynomial, Polynomial, DenseUVPolynomial};
use ark_std::{rand::Rng, vec::Vec, Zero, One, UniformRand};
use ark_bn254::{G1Projective as G1, G2Projective as G2, Bn254, Fr};
use ark_ec::{short_weierstrass::Projective, CurveGroup, Group, AffineRepr};
use ark_ec::pairing::Pairing;
use ark_serialize::CanonicalSerialize; 
use ark_ff::PrimeField; 
use std::ops::{Mul, Sub};
use sha2::{Sha256, Digest};

/// Structured Reference String (SRS) for KZG polynomial commitments
#[derive(Clone, Debug)]
pub struct SRS {
    pub g1: Vec<G1>,  // Generator vector in G1 group
    pub g2: Vec<G2>,  // Generator vector in G2 group
    pub g1_alpha: G1,   // α*G1 (for verification)
    pub g2_alpha: G2,   // α*G2 (for verification)
    pub sum_beta: G1,   // Precomputed Σ(-β^{(N+1)+i}) for verification optimization
}

/// KZG Polynomial Commitment Scheme implementation
#[derive(Clone, Debug)]
pub struct KZG {
    pub srs: SRS,
    pub degree: usize,
}

impl KZG {
    /// Create a new KZG instance
    pub fn new(degree: usize, rng: &mut impl Rng) -> Self {
        // Generate random secret tau (trusted setup)
        let tau = random_scalar(rng);
        let mut g1 = vec![G1::generator()];
        let mut g2 = vec![G2::generator()];
        
        // Generate Structured Reference String (SRS)
        for i in 1..=degree {
            // Use projective coordinate multiplication directly and store in vector (keep as Projective type)
            g1.push(g1[i - 1] * tau);
            g2.push(g2[i - 1] * tau);
        }
        let beta = Fr::one();
        let mut sum_beta = G1::zero();
        let n = degree / 8;
        for i in 0..n {
            sum_beta += g1[n + 1 + i].mul(-beta);
        }
        // Return KZG instance
        KZG {
            srs: SRS {
                g1,
                g2,
                g1_alpha: G1::generator() * tau,
                g2_alpha: G2::generator() * tau,
                sum_beta,
            },
            degree
        }


    }
    
    /// Commit to a polynomial
    /// Parameters:
    /// - vec: Coefficient vector of the polynomial to commit to
    /// Returns: Polynomial commitment (point on G1 group)
    pub fn commit(&self, vec: &[Fr]) -> G1 {
        // Check polynomial degree does not exceed max degree supported by SRS
        assert!(vec.len() <= self.degree + 1, "Vector length exceeds maximum degree supported by SRS");
        
        // Convert vector to polynomial: p(x) = v0 + v1*x + v2*x² + ... + vn*xⁿ
        let poly = DensePolynomial::from_coefficients_vec(vec.to_vec());
        
        // Get polynomial coefficients
        let coeffs = poly.coeffs();
        let mut commitment = G1::zero();  // Initialize commitment as zero element of G1 group
        
        // Compute commitment: sum_{i} (g1_i^{coeff_i})
        for (i, coeff) in coeffs.iter().enumerate() {
            if !coeff.is_zero() {
                commitment += &(self.srs.g1[i] * coeff);
            }
        }
        commitment
    }

    /// Evaluate polynomial at given point
    /// Generate a proof that the value is indeed the polynomial's value at that point
    /// Construct quotient polynomial q(x) = (P(x) - P(z))/(x - z) and commit to q(x)
    pub fn open(&self, poly: &DensePolynomial<Fr>, point: Fr, N: usize) -> (Fr, G1) {
        let value = poly.evaluate(&point);
        
        let coeffs = poly.coeffs();
        let m = coeffs.len();
        let proof = if m <= 1 {
            // Constant polynomial, quotient is zero polynomial
            G1::zero()
        } else {
            let mut q: Vec<Fr> = vec![Fr::zero(); m - 1];
            let mut carry = coeffs[m - 1];
            q[m - 2] = carry;
            for i in (1..(m - 1)).rev() {
                carry = coeffs[i] + point * carry;
                q[i - 1] = carry;
            }
            self.commit_shifted(&q, N)
        };
        
        (value, proof)
    }

    /// Open polynomial with low-degree optimization
    pub fn open_low(&self, poly: &DensePolynomial<Fr>, point: Fr, N: usize) -> (Fr, G1) {
        let value = poly.evaluate(&point);
        
        let coeffs = poly.coeffs();
        let m = coeffs.len();
        let proof = if m <= 1 {
            // Constant polynomial, quotient is zero polynomial
            G1::zero()
        } else {
            let mut q: Vec<Fr> = vec![Fr::zero(); m - 1];
            let mut carry = coeffs[m - 1];
            q[m - 2] = carry;
            for i in (1..(m - 1)).rev() {
                carry = coeffs[i] + point * carry;
                q[i - 1] = carry;
            }
            self.commit_shifted(&q, N+1)
        };
        
        (value, proof)
    }

    /// Verify the opening of a polynomial at a specific point
    /// Parameters:
    /// - commitment: Polynomial commitment
    /// - point: Evaluation point
    /// - value: Claimed value of the polynomial at the point
    /// - proof: Opening proof
    /// Returns: Verification result (bool)
    pub fn verify(
        &self,
        commitment: G1,
        point: Fr,
        value: Fr,
        proof: G1,
    ) -> bool {
        // commitment - v*G1
        let commitment_minus_value = commitment - (self.srs.g1[0] * value);
        // α*G2 - z*G2 (construct difference using power vector in SRS)
        let g2_tau_minus_point = self.srs.g2[1] - (self.srs.g2[0] * point);

        // Convert to affine points for pairing
        let lhs = Bn254::pairing(commitment_minus_value.into_affine(), self.srs.g2[0].into_affine());
        let rhs = Bn254::pairing(proof.into_affine(), g2_tau_minus_point.into_affine());

        lhs == rhs
    }

    // Convenience wrapper: commit polynomial given coefficient slice
    pub fn commit_poly(&self, coeffs: &[Fr]) -> G1 {
        self.commit(coeffs)
    }

    /// Commit coefficients but using SRS generators starting at `shift`.
    /// This produces a commitment to the polynomial \sum_i coeffs[i] * X^{shift + i}
    pub fn commit_shifted(&self, coeffs: &[Fr], shift: usize) -> G1 {
        assert!(shift + coeffs.len() <= self.srs.g1.len(), "shifted range exceeds SRS length");
        let mut commitment = G1::zero();
        for (i, coeff) in coeffs.iter().enumerate() {
            if !coeff.is_zero() {
                commitment += &(self.srs.g1[shift + i] * coeff);
            }
        }
        commitment
    }

    /// Open a (conceptual) shifted polynomial at `point`. Internally builds
    /// the shifted coefficient vector (zeros for indices < shift) and calls `open`.
    pub fn open_shifted_at(&self, coeffs: &[Fr], shift: usize, point: Fr, N: usize) -> (Fr, G1) {
        let mut shifted = vec![Fr::zero(); shift + coeffs.len()];
        for (i, c) in coeffs.iter().enumerate() {
            shifted[shift + i] = *c;
        }
        self.open_at(&shifted, point, N)
    }

    // Open a polynomial (given by coefficient slice) at `point`, returning (value, proof)
    pub fn open_at(&self, coeffs: &[Fr], point: Fr, N: usize) -> (Fr, G1) {
        let poly = DensePolynomial::from_coefficients_vec(coeffs.to_vec());
        self.open(&poly, point, N)
    }

    // Open a polynomial (given by coefficient slice) at `point` with low-degree optimization
    pub fn open_at_low(&self, coeffs: &[Fr], point: Fr, N: usize) -> (Fr, G1) {
        let poly = DensePolynomial::from_coefficients_vec(coeffs.to_vec());
        self.open_low(&poly, point, N)
    }

    // Verify an opening produced by `open`/`open_at`.
    // `commitment` and `proof` are projective G1 points.
    pub fn verify_open(&self, commitment: &G1, point: Fr, value: Fr, proof: &G1) -> bool {
        // reuse existing verify implementation which accepts G1 by value
        self.verify(*commitment, point, value, *proof)
    }

    /// Generate proof for polynomial at specified point (returns proof and computed value)
    pub fn compute_proof(&self, coeffs: &[Fr], point: Fr) -> (Fr, G1) {
        // Compute polynomial value
        let value = evaluate_polynomial(coeffs, point);
        
        // If polynomial length <= 1, return zero proof
        if coeffs.len() <= 1 {
            return (value, G1::zero());
        }
        
        // Compute quotient polynomial q(X) = (f(X) - f(point))/(X - point)
        let q_coeffs = compute_quotient_polynomial(coeffs, point);
        
        // Commit to quotient polynomial as proof
        let proof = self.commit(&q_coeffs);
        
        (value, proof)
    }
    
    /// Generate proof for shifted polynomial
    pub fn compute_shifted_proof(&self, coeffs: &[Fr], shift: usize, point: Fr) -> (Fr, G1) {
        // Build shifted coefficient vector
        let mut shifted_coeffs = vec![Fr::zero(); shift + coeffs.len()];
        for (i, &coeff) in coeffs.iter().enumerate() {
            shifted_coeffs[shift + i] = coeff;
        }
        
        self.compute_proof(&shifted_coeffs, point)
    }
    
    /// Verify proof
    pub fn verify_proof(&self, comm: &G1, point: Fr, value: Fr, proof: &G1) -> bool {
        self.verify(*comm, point, value, *proof)
    }

    
    // Multi-vector commitment: generate independent commitment for each vector (separate mode)
    pub fn commit_vectors_separate(&self, vectors: &[Vec<Fr>]) -> BatchCommitment {
        let mut commitments = Vec::with_capacity(vectors.len());
        for vec in vectors {
            commitments.push(self.commit(vec));
        }
        BatchCommitment { commitments }
    }

    // Multi-vector commitment: aggregated mode (all vectors merged into single polynomial)
    pub fn commit_vectors_aggregated(&self, vectors: &[Vec<Fr>]) -> G1 {
        // Step 1: Align all vector lengths (pad with zeros)
        let max_len = vectors.iter().map(|v| v.len()).max().unwrap_or(0);
        let mut padded_vectors = Vec::new();
        for vec in vectors {
            let mut padded = vec.clone();
            padded.resize(max_len, Fr::zero());
            padded_vectors.push(padded);
        }

        // Step 2: Merge into single polynomial (sum by columns)
        let mut poly_coeffs = vec![Fr::zero(); max_len];
        for (i, coeff) in poly_coeffs.iter_mut().enumerate() {
            for vec in &padded_vectors {
                *coeff += vec[i];
            }
        }

        // Step 3: Generate aggregated commitment
        self.commit(&poly_coeffs)
    }

}

/// Batch commitment for multiple vectors
#[derive(Debug, Clone)]
pub struct BatchCommitment {
    pub commitments: Vec<G1>, // Commitments corresponding to each vector
}

/// Evaluate polynomial at given point
fn evaluate_polynomial(coeffs: &[Fr], point: Fr) -> Fr {
    let mut result = Fr::zero();
    let mut power = Fr::one();
    
    for &coeff in coeffs {
        result += coeff * power;
        power *= point;
    }
    
    result
}

/// Compute quotient polynomial q(X) = (f(X) - f(z))/(X - z)
fn compute_quotient_polynomial(coeffs: &[Fr], point: Fr) -> Vec<Fr> {
    let n = coeffs.len();
    if n <= 1 {
        return vec![Fr::zero()];
    }
    
    let mut q = vec![Fr::zero(); n - 1];
    let mut remainder = coeffs[n - 1];
    
    // Polynomial division: start from highest degree term
    for i in (1..n).rev() {
        if i == n - 1 {
            q[i - 1] = coeffs[i];
        } else {
            q[i - 1] = coeffs[i] + remainder * point;
        }
        remainder = q[i - 1];
    }
    
    q
}

/// Convert G1 point to scalar (simplified implementation, use safer method in production)
pub fn g1_to_scalar(point: &G1) -> Fr {
    let mut bytes = Vec::new();
    point.serialize_compressed(&mut bytes).unwrap();
    let hash = Sha256::digest(&bytes);
    Fr::from_le_bytes_mod_order(&hash)
}
