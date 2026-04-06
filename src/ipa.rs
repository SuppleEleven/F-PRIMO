use ark_ec::AffineRepr;
use ark_bn254::{Bn254, Fr as ScalarField, G1Projective as G1, G2Projective as G2};
use ark_poly::{univariate::DensePolynomial, DenseUVPolynomial, Polynomial};
use ark_poly::domain::EvaluationDomain;
use ark_poly::Radix2EvaluationDomain;
use ark_ec::{pairing::Pairing, CurveGroup, Group, VariableBaseMSM};
use ark_ff::{Field, PrimeField};
use ark_std::{rand::Rng, vec::Vec, vec, UniformRand, Zero, One, ops::Mul};
use std::ops::{Neg, Add, Sub};
use sha2::{Digest, Sha256};
use std::borrow::Borrow;
use ark_serialize::{CanonicalSerialize, CanonicalDeserialize};

type VecFr = Vec<ScalarField>;
type PolyFr = DensePolynomial<ScalarField>;
type CommitmentG1 = <Bn254 as Pairing>::G1Affine;

use crate::kzg::*;

#[derive(Clone, Debug)]
pub struct InnerProductProof {
    pub L_vec: Vec<G1>,
    pub R_vec: Vec<G1>,
    pub a: ScalarField,
    pub b: ScalarField,
    pub g_final: G1,
    pub h_final: G1,
    pub g_commit: CommitmentG1,
    pub h_commit: CommitmentG1,
    pub g_commit_original: CommitmentG1,
    pub h_commit_original: CommitmentG1,
    pub g_value: ScalarField,
    pub h_value: ScalarField,
    pub g_proof: G1,
    pub h_proof: G1,
}

/// Generate inner product proof
pub fn ipa_prove(
    kzg: &KZG,
    transcript: &mut Transcript,
    U: &G1,                    // Additional generator U
    G_factors: &[ScalarField], // Factors of G (usually all 1)
    H_factors: &[ScalarField], // Factors of H (usually powers of y)
    mut G_vec: Vec<G1>,        // Generator vector G
    mut H_vec: Vec<G1>,        // Generator vector H
    mut a_vec: Vec<ScalarField>, // Vector a
    mut b_vec: Vec<ScalarField>, // Vector b
    P: &G1,
) -> Result<InnerProductProof, &'static str> {
    let n = G_vec.len();
    
    let G_Original = G_vec.clone();
    let H_Original = H_vec.clone();

    // Parameter validation
    assert!(n.is_power_of_two(), "Vector length must be a power of two");
    assert_eq!(n, G_vec.len());
    assert_eq!(n, H_vec.len());
    assert_eq!(n, a_vec.len());
    assert_eq!(n, b_vec.len());
    assert_eq!(n, G_factors.len());
    assert_eq!(n, H_factors.len());
    
    // Add domain separator to transcript
    transcript.innerproduct_domain_sep(n as u64);

    // Create slice references for easy splitting
    let mut G = &mut G_vec[..];
    let mut H = &mut H_vec[..];
    let mut a = &mut a_vec[..];
    let mut b = &mut b_vec[..];
    
    let mut current_n = n;
    
    let lg_n = (current_n  as u32).ilog2() as usize;
    let mut L_vec = Vec::with_capacity(lg_n);
    let mut R_vec = Vec::with_capacity(lg_n);

    let mut challenges = Vec::with_capacity(lg_n); // Collect challenge values
    let mut challenges_inv = Vec::with_capacity(lg_n); // Collect inverses of challenges
    
    // Handle first iteration (if n>1)
    if current_n  != 1 {
        current_n = current_n  / 2;
        let (a_L, a_R) = a.split_at_mut(current_n);
        let (b_L, b_R) = b.split_at_mut(current_n);
        let (G_L, G_R) = G.split_at_mut(current_n);
        let (H_L, H_R) = H.split_at_mut(current_n);
        
        let c_L = inner_product(&a_L, &b_R);
        let c_R = inner_product(&a_R, &b_L);
        
        let mut points = Vec::new();
        points.extend_from_slice(G_R);
        points.extend_from_slice(H_L);
        points.push(U.clone());
        let L = variable_base_msm(
            &points,
            &[
                a_L.iter().zip(&G_factors[current_n..2 * current_n]).map(|(a, g)| *a * g).collect::<Vec<_>>(),
                b_R.iter().zip(&H_factors[0..current_n]).map(|(b, h)| *b * h).collect::<Vec<_>>(),
                vec![c_L]
            ].concat(),
        );
        
        let mut points = Vec::new();
        points.extend_from_slice(G_L);
        points.extend_from_slice(H_R);
        points.push(U.clone());
        let R = variable_base_msm(
            &points,
            &[
                a_R.iter().zip(&G_factors[0..current_n]).map(|(a, g)| *a * g).collect::<Vec<_>>(),
                b_L.iter().zip(&H_factors[current_n..2 * current_n]).map(|(b, h)| *b * h).collect::<Vec<_>>(),
                vec![c_R]
            ].concat(),
        );
        
        L_vec.push(L);
        R_vec.push(R);
        
        // Update transcript
        transcript.append_point(b"L", &L);
        transcript.append_point(b"R", &R);
        
        let u = transcript.challenge_scalar(b"u");
        let u_inv = u.inverse().unwrap();
        
        challenges.push(u);
        challenges_inv.push(u_inv);

        // Fold vectors and generators
        for i in 0..current_n {
            a_L[i] = a_L[i] * u + u_inv * a_R[i];
            b_L[i] = b_L[i] * u_inv + u * b_R[i];
            G_L[i] = variable_base_msm(&[G_L[i], G_R[i]], &[u_inv * G_factors[i], u * G_factors[current_n + i]]);
            H_L[i] = variable_base_msm(&[H_L[i], H_R[i]], &[u * H_factors[i], u_inv * H_factors[current_n + i]]);
        }
        // Update slice references
        a = a_L;
        b = b_L;
        G = G_L;
        H = H_L;
    }

    // Main loop
    while current_n  != 1 {
        current_n  = current_n  / 2;
        let (a_L, a_R) = a.split_at_mut(current_n);
        let (b_L, b_R) = b.split_at_mut(current_n);
        let (G_L, G_R) = G.split_at_mut(current_n);
        let (H_L, H_R) = H.split_at_mut(current_n);
        
        let c_L = inner_product(&a_L, &b_R);
        let c_R = inner_product(&a_R, &b_L);
        
        let L_points = [G_R.to_vec(), H_L.to_vec(), vec![*U]].concat();
        let L = variable_base_msm(
            &L_points,
            &[
                a_L.iter().map(|a| *a).collect::<Vec<_>>(),
                b_R.iter().map(|b| *b).collect::<Vec<_>>(),
                vec![c_L]
            ].concat(),
        );
        
        let R_points = [G_L.to_vec(), H_R.to_vec(), vec![*U]].concat();
        let R = variable_base_msm(
            &R_points,
            &[
                a_R.iter().map(|a| *a).collect::<Vec<_>>(),
                b_L.iter().map(|b| *b).collect::<Vec<_>>(),
                vec![c_R]
            ].concat(),
        );

        L_vec.push(L);
        R_vec.push(R);
        
        // Update transcript
        transcript.append_point(b"L", &L);
        transcript.append_point(b"R", &R);
        
        let u = transcript.challenge_scalar(b"u");
        let u_inv = u.inverse().unwrap();
         
        challenges.push(u);
        challenges_inv.push(u_inv);

        // Fold vectors and generators
        for i in 0..current_n {
            a_L[i] = a_L[i] * u + u_inv * a_R[i];
            b_L[i] = b_L[i] * u_inv + u * b_R[i];
            G_L[i] = variable_base_msm(&[G_L[i], G_R[i]], &[u_inv, u]);
            H_L[i] = variable_base_msm(&[H_L[i], H_R[i]], &[u, u_inv]);
        }
        
        // Update slice references
        a = a_L;
        b = b_L;
        G = G_L;
        H = H_L;
    }

    let mut scalars_gf = Vec::new();
    let mut points_gf = Vec::new();
    let mut scalars_hf = Vec::new();
    let mut points_hf = Vec::new();
    scalars_gf.push(a[0]);
    points_gf.push(G[0].clone());

    scalars_hf.push(b[0]);
    points_hf.push(H[0].clone());

    let g_final = variable_base_msm(&points_gf, &scalars_gf);
    let h_final = variable_base_msm(&points_hf, &scalars_hf);

    // Compute g(X) and h(X)
    let g_poly = compute_g_polynomial(&challenges);
    let h_poly = compute_h_polynomial(&challenges, &H_factors, n);
    
    // Generate unpredictable random challenge beta from Fiat-Shamir transcript (prevents prover forgery)
    transcript.append_point(b"g_final", &g_final);
    transcript.append_point(b"h_final", &h_final);
    let beta = transcript.challenge_scalar(b"beta");

    let g_commit = kzg.commit_poly(&g_poly).into_affine();
    let g_commit_original = kzg.commit_poly(&g_poly).into_affine(); // Original commitment
    let (g_value, g_proof) = kzg.open_at_low(&g_poly, beta, n);

    let h_commit = kzg.commit_poly(&h_poly).into_affine();
    let h_commit_original = kzg.commit_shifted(&h_poly, n).into_affine(); // Original commitment
    let (h_value, h_proof) = kzg.open_at(&h_poly, beta, n);

    // Return complete IPA proof containing KZG proofs
    Ok(InnerProductProof{
        L_vec,
        R_vec,
        a: a[0],
        b: b[0],
        g_final,
        h_final,
        g_commit,
        h_commit,
        g_commit_original,
        h_commit_original,
        g_value,
        h_value,
        g_proof,
        h_proof,
    })
}

/// Verify inner product proof
pub fn ipa_verify<IG, IH>(
    kzg: &KZG,
    proof: &InnerProductProof,
    transcript: &mut Transcript,
    n: usize,
    U: &G1,
    G_factors: IG,
    H_factors: IH,
    G: &[G1],
    H: &[G1],
    P: &G1,
) -> Result<bool, &'static str>
where
    IG: IntoIterator,
    IG::Item: Borrow<ScalarField>,
    IH: IntoIterator,
    IH::Item: Borrow<ScalarField>,
{
    // ==============================================
    // Perform traditional IPA verification
    // ==============================================
    // println!("Starting IPA verification");
    transcript.innerproduct_domain_sep(n as u64);

    let lg_n = proof.L_vec.len();
    if lg_n >= 32 {
        println!("Proof is too large");
        return Err("Proof is too large");
    }
    if n != (1 << lg_n) {
        println!("Length mismatch");
        return Err("Length mismatch");
    }

    // 1. Recompute challenge values
    let mut challenges = Vec::with_capacity(lg_n);
    for (L, R) in proof.L_vec.iter().zip(proof.R_vec.iter()) {
        transcript.append_point(b"L", L);
        transcript.append_point(b"R", R);
        challenges.push(transcript.challenge_scalar(b"u"));
    }

    // 2. Compute inverses of challenges
    let mut challenges_inv = challenges.clone();
    let allinv = ScalarField::batch_inverse(&mut challenges_inv).ok_or("Inverse computation failed")?;

    // 3. Compute squares and inverse squares of challenges
    let challenges_sq: Vec<ScalarField> = challenges.iter().map(|u| u.square()).collect();
    let challenges_inv_sq: Vec<ScalarField> = challenges_inv.iter().map(|u| u.square()).collect();
    
    // Convert factors to vectors for indexed access
    let g_factors: Vec<ScalarField> = G_factors.into_iter().map(|x| *x.borrow()).collect();
    let h_factors: Vec<ScalarField> = H_factors.into_iter().map(|x| *x.borrow()).collect();
    
    // Check lengths
    if g_factors.len() != n || h_factors.len() != n {
        println!("Factor length mismatch");
        return Err("Factor length mismatch");
    }

    // Scalar components
    let mut scalars = Vec::new();
    let mut points = Vec::new();
    
    // a*b * U
    scalars.push(proof.a * proof.b);
    points.push(U.clone());
    
    // -u_sq[i] * L_i
    for (i, L) in proof.L_vec.iter().enumerate() {
        scalars.push(-challenges_sq[i]);
        points.push(L.clone());
    }
    
    // -u_inv_sq[i] * R_i
    for (i, R) in proof.R_vec.iter().enumerate() {
        scalars.push(-challenges_inv_sq[i]);
        points.push(R.clone());
    }
    
    // Compute multi-scalar multiplication
    let affine_points: Vec<_> = points.iter().map(|p| p.into_affine()).collect();
    
    let c = variable_base_msm(&points, &scalars);
    let expected_P = c + proof.g_final + proof.h_final;

    // Verify equality
    let result = expected_P == *P;

    // ==============================================
    // Verify validity of g_final/h_final
    // ==============================================
    // Verifier recomputes value
    // Compute g(X) and h(X)
    let g_poly = compute_g_polynomial(&challenges);
    let h_poly = compute_h_polynomial(&challenges, &h_factors, n);
    
    // Exact same transcript flow as prover to regenerate challenge z (ensures unpredictability)
    // Continue transcript to generate identical beta as prover
    transcript.append_point(b"g_final", &proof.g_final);
    transcript.append_point(b"h_final", &proof.h_final);
    let beta = transcript.challenge_scalar(b"beta");
    
    let g_value = g_poly.evaluate(&beta);
    let h_value = h_poly.evaluate(&beta);

    if !verify_open_with_degree_bound(
        kzg,
        &proof.g_commit,
        beta,
        g_value,
        &proof.g_proof,
        n, 
        false
    ) {
        return Err("Degree bound verification failed for g_final");
    }

    if !verify_open_with_degree_bound(
        kzg,
        &proof.h_commit,
        beta,
        h_value,
        &proof.h_proof,
        n, 
        true 
    ) {
        return Err("Shifted polynomial verification failed for h_final");
    }

    // For high-degree polynomial f(X) = X^{N+1} * f'(X), check e([f(β)]_1, [1]_2) ?= e([f'(β)]_1, [β^{N+1}]_2)
    // Get G2 element for β^{N+1}
    if n + 1 >= kzg.srs.g2.len() {
        return Err("SRS does not contain G2 element for β^{}");
    }
    
    let beta_pow_N_plus_1 = kzg.srs.g2[n].into_affine();
    
    let left_pairing = Bn254::pairing(
        proof.h_commit_original,
        kzg.srs.g2[0].into_affine()
    );
    
    let right_pairing = Bn254::pairing(
        proof.h_commit,
        beta_pow_N_plus_1
    );
    
    if left_pairing != right_pairing {
        return Err("IPA correctness verification failed");
    }
   
    Ok(result)
}

/// Compute g(X) polynomial
/// g(X) = X * ∏_{i=1}^{r} (x_i^{-1} + x_i * X^{2^{r-i}})
pub fn compute_g_polynomial(
    challenges: &[ScalarField],  // x_1, x_2, ..., x_r
) -> DensePolynomial<ScalarField> {
    let r = challenges.len();
    if r == 0 {
        // If r=0, return X
        let mut coeffs = vec![ScalarField::zero(); 2];
        coeffs[1] = ScalarField::one(); // Coefficient of X
        return DensePolynomial::from_coefficients_vec(coeffs);
    }

    // Initial value is 1 (polynomial multiplication identity)
    let mut result = DensePolynomial::from_coefficients_vec(vec![ScalarField::one()]);
    
    for (i, x_i) in challenges.iter().enumerate() {
        let i = i + 1; // 1-indexed
        let exp = 1usize << (r - i); // 2^{r-i}
        
        // Construct (x_i^{-1} + x_i * X^{exp})
        let x_inv = x_i.inverse().unwrap();
        let x = *x_i;
        
        // Polynomial: x_i^{-1} + x_i * X^{exp}
        let mut term_coeffs = vec![ScalarField::zero(); exp + 1];
        term_coeffs[0] = x_inv;        // Coefficient of X^0
        term_coeffs[exp] = x;          // Coefficient of X^{exp}
        
        let term = DensePolynomial::from_coefficients_vec(term_coeffs);
        
        // Multiply accumulatively
        result = &result * &term;
    }
    
    // Multiply by X
    let mut final_coeffs = vec![ScalarField::zero(); result.coeffs.len() + 1];
    for (i, coeff) in result.coeffs.iter().enumerate() {
        final_coeffs[i + 1] = *coeff;
    }
    
    DensePolynomial::from_coefficients_vec(final_coeffs)
}

/// Compute h(X) polynomial
/// h(X) = X^{2} * ∏_{i=1}^{r} (x_i + x_i^{-1} * y^{-2^{r-i}} * X^{2^{r-i}})
pub fn compute_h_polynomial(
    challenges: &[ScalarField],  // x_1, x_2, ..., x_r
    H_factors: &[ScalarField],   // H_factors[j] = y^{-j}
    n: usize,                    // Vector length N
) -> DensePolynomial<ScalarField> {
    let r = challenges.len();
    let shift = 2; // N+2 - N
    
    if r == 0 {
        let mut coeffs = vec![ScalarField::zero(); shift + 1];
        coeffs[shift] = ScalarField::one();
        return DensePolynomial::from_coefficients_vec(coeffs);
    }

    let mut result = DensePolynomial::from_coefficients_vec(vec![ScalarField::one()]);
    
    for (i, x_i) in challenges.iter().enumerate() {
        let i = i + 1; // 1-indexed
        let exp = 1usize << (r - i); // 2^{r-i}
        
        // Get y^{-2^{r-i}} from H_factors
        // H_factors[exp] = y^{-exp} = y^{-2^{r-i}}
        let y_exp_inv = H_factors[exp];
        
        // Construct (x_i + x_i^{-1} * y^{-2^{r-i}} * X^{exp})
        let x_inv = x_i.inverse().unwrap();
        let x = *x_i;
        
        // Coefficient: x_i^{-1} * y^{-2^{r-i}}
        let coeff = x_inv * y_exp_inv;
        
        // Polynomial: x_i + coeff * X^{exp}
        let mut term_coeffs = vec![ScalarField::zero(); exp + 1];
        term_coeffs[0] = x;            // Coefficient of X^0
        term_coeffs[exp] = coeff;      // Coefficient of X^{exp}
        
        let term = DensePolynomial::from_coefficients_vec(term_coeffs);
        
        // Multiply accumulatively
        result = &result * &term;
    }
    
    // Multiply by X^{N+2}
    let mut final_coeffs = vec![ScalarField::zero(); result.coeffs.len() + shift];
    for (i, coeff) in result.coeffs.iter().enumerate() {
        final_coeffs[i + shift] = *coeff;
    }
    
    DensePolynomial::from_coefficients_vec(final_coeffs)
}

pub fn verify_open_with_degree_bound(
    kzg: &KZG,
    comm: &CommitmentG1,
    point: ScalarField,
    value: ScalarField,
    proof: &G1,
    total_degree: usize,  // Total degree bound N
    is_high_degree: bool, // Whether it's a high-degree polynomial (requires factor extraction)
) -> bool {
    if !is_high_degree {
        // For low-degree polynomials (degree < N): enforce degree bound by adjusting verification equation
        // Replace proof with [q(β)·β^{2N - deg + 1}]_1
        
        // Compute degree_diff = 2N - deg + 1
        let degree_diff = total_degree + 1;
        
        // After adjustment: e(C - [value]_1, [β^{degree_diff}]_2) ?= e(proof, [β - point]_2)
        if degree_diff >= kzg.srs.g2.len() { return false; }// SRS does not contain sufficiently high powers
        
        let beta_pow_deg_diff = kzg.srs.g2[degree_diff].into_affine();
        let beta_minus_point_g2 = kzg.srs.g2[0].mul(point.neg()).add(&kzg.srs.g2[1]);
        
        let left_pairing = Bn254::pairing(
            (G1::from(*comm) - G1::generator().mul(value)).into_affine(),
            beta_pow_deg_diff
        );
        
        let right_pairing = Bn254::pairing(*proof, beta_minus_point_g2.into_affine());
        
        return left_pairing == right_pairing;
    }
    else {
        // For low-degree polynomials (degree < N): enforce degree bound by adjusting verification equation
        // Replace proof with [q(β)·β^{2N - deg + 1}]_1
        
        // Compute degree_diff = 2N - deg + 1
        let degree_diff = total_degree;
        
        // After adjustment: e(C - [value]_1, [β^{degree_diff}]_2) ?= e(proof, [β - point]_2)
        if degree_diff >= kzg.srs.g2.len() { return false; }// SRS does not contain sufficiently high powers
        
        let beta_pow_deg_diff = kzg.srs.g2[degree_diff].into_affine();
        let beta_minus_point_g2 = kzg.srs.g2[0].mul(point.neg()).add(&kzg.srs.g2[1]);
        
        let left_pairing = Bn254::pairing(
            (G1::from(*comm) - G1::generator().mul(value)).into_affine(),
            beta_pow_deg_diff
        );
        
        let right_pairing = Bn254::pairing(*proof, beta_minus_point_g2.into_affine());
        
        return left_pairing == right_pairing;
    }
}

/// Transcript used for Fiat-Shamir transformation
pub struct Transcript {
    state: Sha256,
    has_challenged: bool,
}

impl Transcript {
    pub fn new(label: &[u8]) -> Self {
        let mut state = Sha256::new();
        state.update(label);
        Transcript {
            state,
            has_challenged: false,
        }
    }
    
    pub fn innerproduct_domain_sep(&mut self, n: u64) {
        self.append_message(b"dom-sep", b"inner-product");
        self.append_u64(b"n", n);
    }
    
    pub fn append_u64(&mut self, label: &[u8], value: u64) {
        self.state.update(label);
        self.state.update(value.to_le_bytes());
    }
    
    pub fn append_message(&mut self, label: &[u8], message: &[u8]) {
        self.state.update(label);
        self.state.update(message);
    }

    pub fn append_scalar(&mut self, label: &[u8], scalar: &ScalarField) {
        self.state.update(label);
        let mut bytes = Vec::new();
        scalar.serialize_compressed(&mut bytes).unwrap();
        self.state.update(bytes);
    }

    pub fn append_point(&mut self, label: &[u8], point: &G1) {
        self.state.update(label);
        let mut bytes = Vec::new();
        point.serialize_compressed(&mut bytes).unwrap();
        self.state.update(bytes);
    }
    
    pub fn challenge_scalar(&mut self, label: &[u8]) -> ScalarField {
        self.state.update(label);
        
        // If already challenged, add counter to ensure uniqueness
        if self.has_challenged {
            let counter = self.state.clone().finalize();
            self.state.update(&counter);
        }
        
        let result = self.state.clone().finalize();
        self.has_challenged = true;
        
        // Add challenge result to transcript to ensure different subsequent challenges
        self.state.update(&result);
        
        ScalarField::from_le_bytes_mod_order(&result)
    }
}

/// Batch compute inverses of scalars
pub trait BatchInverse {
    fn batch_inverse(v: &mut [Self]) -> Option<Self> where Self: Sized;
}

impl BatchInverse for ScalarField {
    fn batch_inverse(v: &mut [Self]) -> Option<Self> {
        if v.is_empty() {
            return Some(ScalarField::one());
        }
        
        let n = v.len();
        let mut products = vec![ScalarField::zero(); n];
        products[0] = v[0];
        
        for i in 1..n {
            products[i] = products[i-1] * v[i];
        }
        
        let all_inv = products[n-1].inverse()?;
        
        let mut inv = all_inv;
        for i in (1..n).rev() {
            let temp = v[i];
            v[i] = products[i-1] * inv;
            inv = inv * temp;
        }
        
        v[0] = inv;
        Some(all_inv)
    }
}

/// Variable-base multi-scalar multiplication
fn variable_base_msm(points: &[G1], scalars: &[ScalarField]) -> G1 {
    assert_eq!(points.len(), scalars.len(), "Points and scalars count mismatch");

    if points.is_empty() {
        return G1::zero();
    }
    // Convert Projective points to Affine form
    let affine_points: Vec<_> = points.iter().map(|p| p.into_affine()).collect();
    // Compute using MSM
    G1::msm_unchecked(&affine_points, scalars)
}

/// Compute inner product
pub fn inner_product(a: &[ScalarField], b: &[ScalarField]) -> ScalarField {
    assert_eq!(a.len(), b.len(), "Vector length mismatch");
    a.iter()
        .zip(b.iter())
        .map(|(x, y)| *x * *y)
        .sum()
}

impl InnerProductProof {
    /// Get serialized size of the proof
    pub fn serialized_size(&self) -> usize {
        assert_eq!(self.L_vec.len(), self.R_vec.len());
        let point_size = 32; // Compressed G1 size (ark-bn254 standard)
        let scalar_size = 32; // Compressed Scalar size (ark-bn254 standard)
        self.L_vec.len() * 2 * point_size + 4 * scalar_size + 8 * point_size
    }
    
    /// Serialize proof to bytes
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut buf = Vec::with_capacity(self.serialized_size());
        
        // Serialize L_vec and R_vec
        for (l, r) in self.L_vec.iter().zip(self.R_vec.iter()) {
            let mut l_bytes = Vec::new();
            l.serialize_compressed(&mut l_bytes).unwrap();
            let mut r_bytes = Vec::new();
            r.serialize_compressed(&mut r_bytes).unwrap();

            buf.extend(l_bytes);
            buf.extend(r_bytes);
        }
        
        // Serialize a and b
        let mut a_bytes = Vec::new();
        self.a.serialize_compressed(&mut a_bytes).unwrap();

        let mut b_bytes = Vec::new();
        self.b.serialize_compressed(&mut b_bytes).unwrap();

        buf.extend(a_bytes);
        buf.extend(b_bytes);

        // Serialize other G1 points
        let points = [
            &self.g_final,
            &self.h_final,
            &G1::from(self.g_commit),
            &G1::from(self.h_commit),
            &G1::from(self.g_commit_original),
            &G1::from(self.h_commit_original),
            &self.g_proof,
            &self.h_proof,
        ];
        
        for point in points.iter() {
            let mut bytes = Vec::new();
            point.serialize_compressed(&mut bytes).unwrap();
            buf.extend(bytes);
        }
        
        // Serialize scalar values
        let mut g_value_bytes = Vec::new();
        self.g_value.serialize_compressed(&mut g_value_bytes).unwrap();
        buf.extend(g_value_bytes);
        
        let mut h_value_bytes = Vec::new();
        self.h_value.serialize_compressed(&mut h_value_bytes).unwrap();
        buf.extend(h_value_bytes);
        
        buf
    }

    /// Deserialize proof from bytes
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, &'static str> {
        let mut cursor = 0;
        let point_size = 32; // Compressed size of G1 point
        let scalar_size = 32; // Size of scalar
        
        // Calculate total size of fixed fields: 4 scalars + 8 G1 points
        let fixed_fields_size = 4 * scalar_size + 8 * point_size;
        
        // Calculate total bytes for L_vec and R_vec
        let vec_bytes_total = bytes.len().checked_sub(fixed_fields_size)
            .ok_or("Insufficient byte data length")?;
        
        // Calculate vector length (each vector element occupies 2 G1 points)
        if vec_bytes_total % (2 * point_size) != 0 {
            return Err("Vector byte length mismatch");
        }
        let vec_len = vec_bytes_total / (2 * point_size);
        
        let mut L_vec = Vec::with_capacity(vec_len);
        let mut R_vec = Vec::with_capacity(vec_len);
        
        // Deserialize L_vec and R_vec
        for _ in 0..vec_len {
            if cursor + point_size > bytes.len() {
                return Err("Insufficient byte data");
            }
            
            // Deserialize L point
            let l_bytes = &bytes[cursor..cursor + point_size];
            let l = G1::deserialize_compressed(l_bytes).map_err(|_| "Failed to deserialize L point")?;
            L_vec.push(l);
            cursor += point_size;
            
            // Deserialize R point
            let r_bytes = &bytes[cursor..cursor + point_size];
            let r = G1::deserialize_compressed(r_bytes).map_err(|_| "Failed to deserialize R point")?;
            R_vec.push(r);
            cursor += point_size;
        }
        
        // Deserialize a and b
        if cursor + 2 * scalar_size > bytes.len() {
            return Err("Insufficient byte data");
        }
        
        let a_bytes = &bytes[cursor..cursor + scalar_size];
        let a = ScalarField::deserialize_compressed(a_bytes).map_err(|_| "Failed to deserialize scalar a")?;
        cursor += scalar_size;
        
        let b_bytes = &bytes[cursor..cursor + scalar_size];
        let b = ScalarField::deserialize_compressed(b_bytes).map_err(|_| "Failed to deserialize scalar b")?;
        cursor += scalar_size;

        // Deserialize G1 points
        let mut deserialize_g1 = || -> Result<G1, &'static str> {
            if cursor + point_size > bytes.len() {
                return Err("Insufficient G1 point byte data");
            }
            let bytes_slice = &bytes[cursor..cursor + point_size];
            cursor += point_size;
            G1::deserialize_compressed(bytes_slice).map_err(|_| "Failed to deserialize G1 point")
        };
        
        let g_final = deserialize_g1()?;
        let h_final = deserialize_g1()?;
        let g_commit_g1 = deserialize_g1()?;
        let h_commit_g1 = deserialize_g1()?;
        let g_commit_original_g1 = deserialize_g1()?;
        let h_commit_original_g1 = deserialize_g1()?;
        let g_proof = deserialize_g1()?;
        let h_proof = deserialize_g1()?;
        
        // Deserialize g_value and h_value
        if cursor + 2 * scalar_size > bytes.len() {
            return Err("Insufficient value scalar byte data");
        }
        
        let g_value_bytes = &bytes[cursor..cursor + scalar_size];
        let g_value = ScalarField::deserialize_compressed(g_value_bytes).map_err(|_| "Failed to deserialize g_value")?;
        cursor += scalar_size;

        let h_value_bytes = &bytes[cursor..cursor + scalar_size];
        let h_value = ScalarField::deserialize_compressed(h_value_bytes).map_err(|_| "Failed to deserialize h_value")?;
        cursor += scalar_size;
        
        // Convert to Affine commitments
        let g_commit = g_commit_g1.into_affine();
        let h_commit = h_commit_g1.into_affine();
        let g_commit_original = g_commit_original_g1.into_affine();
        let h_commit_original = h_commit_original_g1.into_affine();
        
        Ok(InnerProductProof{
            L_vec,
            R_vec,
            a,
            b,
            g_final,
            h_final,
            g_commit,
            h_commit,
            g_commit_original,
            h_commit_original,
            g_value,
            h_value,
            g_proof,
            h_proof,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_std::rand::RngCore;
    use ark_std::test_rng;
    use rand::rngs::StdRng;
    use ark_ff::UniformRand;

    // Test helper: generate random vector
    fn random_scalar_vec<R: RngCore>(rng: &mut R, len: usize) -> Vec<ScalarField> {
        (0..len).map(|_| ScalarField::rand(rng)).collect()
    }

    // Test helper: generate random G1 point vector
    fn random_g1_vec<R: RngCore>(rng: &mut R, len: usize) -> Vec<G1> {
        (0..len).map(|_| G1::rand(rng)).collect()
    }

    // Test complete IPA proof protocol
    #[test]
    fn test_ipa_full_protocol() {
        let mut rng = test_rng();

        // Test different n values - explicitly specified as usize type
        let test_cases: [usize; 5] = [1, 2, 4, 32, 64];
        
        for &n in &test_cases {
            println!("------------------Testing n = {}----------------------", n);
            
            let degree = n * 8;
            let kzg = KZG::new(degree , &mut rng);
            let x = ScalarField::rand(&mut rng);
            // Generate test data
            let a_vec = random_scalar_vec(&mut rng, n);
            let b_vec = random_scalar_vec(&mut rng, n);
            let U = kzg.srs.g1[n] * x;
            
            // Compute powers of y as H_factors
            let y = ScalarField::rand(&mut rng);
            let y_inv = y.inverse().expect("y cannot be zero, protocol guarantees non-zero challenge");
            let H_factors: Vec<ScalarField> = (0..n).map(|i| y_inv.pow([i as u64])).collect();
            
            let G_factors = vec![ScalarField::one(); n];

            let g_vec_affine: Vec<CommitmentG1> = (1..=n)
                .map(|i| kzg.srs.g1[i].into_affine())
                .collect();
            let h_vec_affine: Vec<CommitmentG1> = (1..=n)
                .map(|i| {
                    let y_power = if i == 1 {
                        ScalarField::one()
                    } else {
                        y_inv.pow([(i - 1) as u64])
                    };
                    let exponent = n + 1 + i;
                    kzg.srs.g1[exponent].mul(y_power).into_affine()
                })
                .collect();
            let G_vec: Vec<G1> = g_vec_affine.iter().map(|x| x.into_group()).collect();
            let H_vec: Vec<G1> = h_vec_affine.iter().map(|x| x.into_group()).collect();
    
            // P = <a, G> + <b_prime, H> + <a,b> * U
            // where b_prime[i] = b[i] * y_inv^i
            let b_prime: Vec<ScalarField> = b_vec.iter()
                .enumerate()
                .map(|(i, b_i)| *b_i * H_factors[i])  // H_factors[i] = y_inv^i
                .collect();
            
            let c = inner_product(&a_vec, &b_vec);

            // Compute commitment P = <a, G> + <b_prime, H> + c * U
            let aG = variable_base_msm(&G_vec, &a_vec);
            let b_prime_H = variable_base_msm(&H_vec, &b_prime);
            let cU = U.mul(c);
            
            let P = aG + b_prime_H + cU;

            // Generate random beta
            let beta = ScalarField::rand(&mut rng);
            
            // Generate proof
            let mut transcript_prover = Transcript::new(b"full_protocol_test");
            let proof = ipa_prove(
                &kzg,
                &mut transcript_prover,
                &U,
                &G_factors,
                &H_factors,
                G_vec.clone(),
                H_vec.clone(),
                a_vec.clone(),
                b_vec.clone(),
                &P,
            ).expect("Proof generation failed");
            
            // Verify proof
            let mut transcript_verifier = Transcript::new(b"full_protocol_test");
            let result = ipa_verify(
                &kzg,
                &proof,
                &mut transcript_verifier,
                n,
                &U,
                &G_factors,
                &H_factors,
                &G_vec,
                &H_vec,
                &P,
            );
            
            match result {
                Ok(is_valid) => {
                    if is_valid {
                        println!("Proof verification succeeded for n={}", n);
                    } else {
                        println!("Proof verification failed for n={}", n);
                    }
                    assert!(is_valid, "Proof verification failed for n={}", n)
                },
                Err(e) => panic!("Verification error for n={}: {}", n, e),
            }
        }
    }
    
    // Test batch inverse computation
    #[test]
    fn test_batch_inverse() {
        let scalars = vec![
            ScalarField::from(2u64),
            ScalarField::from(3u64),
            ScalarField::from(5u64),
        ];
        
        let mut v = scalars.clone();
        let allinv = ScalarField::batch_inverse(&mut v).unwrap();
        
        // Check each inverse is correct
        for i in 0..scalars.len() {
            assert_eq!(v[i] * scalars[i], ScalarField::one());
        }
        
        // Check inverse of product of all elements is correct
        let mut product = ScalarField::one();
        for s in &scalars {
            product *= s;
        }
        assert_eq!(allinv, product.inverse().unwrap());
    }

    // Test inner product computation
    #[test]
    fn test_inner_product() {
        let a = vec![
            ScalarField::from(1u64),
            ScalarField::from(2u64),
            ScalarField::from(3u64),
            ScalarField::from(4u64),
        ];
        let b = vec![
            ScalarField::from(2u64),
            ScalarField::from(3u64),
            ScalarField::from(4u64),
            ScalarField::from(5u64),
        ];
        let expected = ScalarField::from(40u64);
        assert_eq!(expected, inner_product(&a, &b));
    }

    // Test edge case: inner product of empty vectors
    #[test]
    fn test_inner_product_empty() {
        let a: Vec<ScalarField> = vec![];
        let b: Vec<ScalarField> = vec![];
        
        let result = inner_product(&a, &b);
        assert_eq!(result, ScalarField::zero());
    }

    // Test edge case: vector of length 1
    #[test]
    fn test_inner_product_single() {
        let mut rng = test_rng();
        let a = vec![ScalarField::rand(&mut rng)];
        let b = vec![ScalarField::rand(&mut rng)];
        
        let result = inner_product(&a, &b);
        assert_eq!(result, a[0] * b[0]);
    }
    
    // Test variable-base multi-scalar multiplication
    #[test]
    fn test_variable_base_msm() {
        let mut rng = test_rng();
        let n: usize = 4;
        
        let points = random_g1_vec(&mut rng, n);
        let scalars = random_scalar_vec(&mut rng, n);
        
        let msm_result = variable_base_msm(&points, &scalars);
        
        let affine_points: Vec<_> = points.iter().map(|p| p.into_affine()).collect();
        let ark_result = G1::msm_unchecked(&affine_points, &scalars);
        
        assert_eq!(msm_result, ark_result);
    }

    // Test edge case: variable-base multi-scalar multiplication with empty input
    #[test]
    fn test_variable_base_msm_empty() {
        let points: Vec<G1> = vec![];
        let scalars: Vec<ScalarField> = vec![];
        
        let result = variable_base_msm(&points, &scalars);
        assert_eq!(result, G1::zero());
    }

    // Test edge case: variable-base multi-scalar multiplication with single input
    #[test]
    fn test_variable_base_msm_single() {
        let mut rng = test_rng();
        let point = G1::rand(&mut rng);
        let scalar = ScalarField::rand(&mut rng);
        
        let result = variable_base_msm(&[point], &[scalar]);
        let expected = point.mul(scalar);
        
        assert_eq!(result, expected);
    }

    // Test that faulty proofs are rejected
    #[test]
    fn test_ipa_faulty_proof() {
        let mut rng = test_rng();
        let n: usize = 4;
        
        // Initialize KZG
        let srs_degree: usize = 10;
        let kzg = KZG::new(srs_degree, &mut rng);
        
        // Generate correct test data
        let G_vec = random_g1_vec(&mut rng, n);
        let H_vec = random_g1_vec(&mut rng, n);
        let a_vec = random_scalar_vec(&mut rng, n);
        let b_vec = random_scalar_vec(&mut rng, n);
        let U = G1::rand(&mut rng);
        
        // Compute powers of y as H_factors
        let y = ScalarField::rand(&mut rng);
        let y_inv = y.inverse().expect("y cannot be zero, protocol guarantees non-zero challenge");
        let H_factors: Vec<ScalarField> = (0..n).map(|i| y_inv.pow([i as u64])).collect();
        let G_factors = vec![ScalarField::one(); n];
        
        let c = inner_product(&a_vec, &b_vec);
        let mut P = variable_base_msm(&G_vec, &a_vec);
        let bH = variable_base_msm(&H_vec, &b_vec);
        let cU = U.mul(c);
        P += bH + cU;
        
        // Generate correct proof
        let beta = ScalarField::rand(&mut rng);
        let mut transcript_prover = Transcript::new(b"test_transcript");
        let proof = ipa_prove(
            &kzg,
            &mut transcript_prover,
            &U,
            &G_factors,
            &H_factors,
            G_vec.clone(),
            H_vec.clone(),
            a_vec.clone(),
            b_vec.clone(),
            &P,
        ).expect("Proof generation failed");
        
        // Test 1: Tamper with proof data
        let mut faulty_proof1 = proof.clone();
        faulty_proof1.a += ScalarField::one();
        
        let mut transcript_verifier1 = Transcript::new(b"test_transcript");
        let result1 = ipa_verify(
            &kzg,
            &faulty_proof1,
            &mut transcript_verifier1,
            n,
            &U,
            &G_factors,
            &H_factors,
            &G_vec,
            &H_vec,
            &P,
        );
        
        match result1 {
            Ok(is_valid) => assert!(!is_valid, "Proof with tampered a value should be rejected"),
            Err(_) => (),
        }
        
        // Test 2: Tamper with b value
        let mut faulty_proof2 = proof.clone();
        faulty_proof2.b += ScalarField::one();
        
        let mut transcript_verifier2 = Transcript::new(b"test_transcript");
        let result2 = ipa_verify(
            &kzg,
            &faulty_proof2,
            &mut transcript_verifier2,
            n,
            &U,
            &G_factors,
            &H_factors,
            &G_vec,
            &H_vec,
            &P,
        );

        match result2 {
            Ok(is_valid) => assert!(!is_valid, "Proof with tampered b value should be rejected"),
            Err(_) => (),
        }
        
        // Test 3: Tamper with KZG values
        let mut faulty_proof3 = proof.clone();
        faulty_proof3.g_final += G1::generator();
        
        let mut transcript_verifier3 = Transcript::new(b"test_transcript");
        let result3 = ipa_verify(
            &kzg,
            &faulty_proof3,
            &mut transcript_verifier3,
            n,
            &U,
            &G_factors,
            &H_factors,
            &G_vec,
            &H_vec,
            &P,
        );
        
        match result3 {
            Ok(is_valid) => assert!(!is_valid, "Proof with tampered KZG values should be rejected"),
            Err(_) => (),
        }
    }

    // Test Transcript correctness
    #[test]
    fn test_transcript() {
        let mut transcript = Transcript::new(b"test");
        
        transcript.append_u64(b"n", 8);
        transcript.append_message(b"msg", b"hello");
        
        let scalar = ScalarField::from(42u64);
        transcript.append_scalar(b"scalar", &scalar);
        
        let point = G1::generator();
        transcript.append_point(b"point", &point);
        
        let challenge1 = transcript.challenge_scalar(b"challenge1");
        let challenge2 = transcript.challenge_scalar(b"challenge2");
        
        assert_ne!(challenge1, challenge2);
        
        let mut transcript2 = Transcript::new(b"test");
        transcript2.append_u64(b"n", 8);
        transcript2.append_message(b"msg", b"hello");
        transcript2.append_scalar(b"scalar", &scalar);
        transcript2.append_point(b"point", &point);
        
        let challenge1_2 = transcript2.challenge_scalar(b"challenge1");
        assert_eq!(challenge1, challenge1_2);
    }

    // Test Transcript domain separator
    #[test]
    fn test_transcript_domain_sep() {
        let mut transcript1 = Transcript::new(b"test");
        transcript1.innerproduct_domain_sep(8);
        let challenge1 = transcript1.challenge_scalar(b"challenge");
        
        let mut transcript2 = Transcript::new(b"test");
        transcript2.innerproduct_domain_sep(16); // Different n value
        let challenge2 = transcript2.challenge_scalar(b"challenge");
        
        assert_ne!(challenge1, challenge2, "Different domain separators should produce different challenges");
    }

    // Test multiple Transcript challenges
    #[test]
    fn test_transcript_multiple_challenges() {
        let mut transcript = Transcript::new(b"test");
        
        let challenge1 = transcript.challenge_scalar(b"challenge1");
        let challenge2 = transcript.challenge_scalar(b"challenge2");
        let challenge3 = transcript.challenge_scalar(b"challenge3");
        
        assert_ne!(challenge1, challenge2);
        assert_ne!(challenge2, challenge3);
        assert_ne!(challenge1, challenge3);
    }

    // Test wrong transcript label
    #[test]
    fn test_ipa_wrong_transcript_label() {
        let mut rng = test_rng();
        let n: usize = 4;
        
        // Initialize KZG
        let srs_degree = n*8;
        let kzg = KZG::new(srs_degree, &mut rng);
        
        // Generate test data
        let G_vec = random_g1_vec(&mut rng, n);
        let H_vec = random_g1_vec(&mut rng, n);
        let a_vec = random_scalar_vec(&mut rng, n);
        let b_vec = random_scalar_vec(&mut rng, n);
        let U = G1::rand(&mut rng);
        
        // Compute powers of y as H_factors
        let y = ScalarField::rand(&mut rng);
        let y_inv = y.inverse().expect("y cannot be zero, protocol guarantees non-zero challenge");
        let H_factors: Vec<ScalarField> = (0..n).map(|i| y_inv.pow([i as u64])).collect();
        
        let G_factors = vec![ScalarField::one(); n];
        
        let c = inner_product(&a_vec, &b_vec);
        let mut P = variable_base_msm(&G_vec, &a_vec);
        let bH = variable_base_msm(&H_vec, &b_vec);
        let cU = U.mul(c);
        P += bH + cU;
        
        // Generate proof (using label1)
        let beta = ScalarField::rand(&mut rng);
        let mut transcript_prover = Transcript::new(b"label1");
        let proof = ipa_prove(
            &kzg,
            &mut transcript_prover,
            &U,
            &G_factors,
            &H_factors,
            G_vec.clone(),
            H_vec.clone(),
            a_vec.clone(),
            b_vec.clone(),
            &P,
        ).expect("Proof generation failed");
        
        // Use different label for verification
        let mut transcript_verifier = Transcript::new(b"label2");
        let result = ipa_verify(
            &kzg,
            &proof,
            &mut transcript_verifier,
            n,
            &U,
            &G_factors,
            &H_factors,
            &G_vec,
            &H_vec,
            &P,
        );
        
        match result {
            Ok(is_valid) => assert!(!is_valid, "Different transcript labels should be rejected"),
            Err(_) => (),
        }
    }

    // Test serialization and deserialization of IPA proof
    #[test]
    fn test_ipa_serialization() {
        let mut rng = test_rng();

        // Test proofs of different sizes
        for size in [0, 1, 3, 7, 15] {
            println!("Testing proof size: {}", size);
            
            // Create mock IPA proof - using corrected struct fields
            let proof = InnerProductProof {
                L_vec: random_g1_vec(&mut rng, size),
                R_vec: random_g1_vec(&mut rng, size),
                a: ScalarField::rand(&mut rng),
                b: ScalarField::rand(&mut rng),
                g_final: G1::rand(&mut rng),
                h_final: G1::rand(&mut rng),
                // KZG related fields
                g_commit: G1::rand(&mut rng).into_affine(),
                h_commit: G1::rand(&mut rng).into_affine(),
                g_commit_original: G1::rand(&mut rng).into_affine(),
                h_commit_original: G1::rand(&mut rng).into_affine(),
                g_value: ScalarField::rand(&mut rng),
                h_value: ScalarField::rand(&mut rng),
                g_proof: G1::rand(&mut rng),
                h_proof: G1::rand(&mut rng),
            };
            
            // Serialize
            let bytes = proof.to_bytes();
            println!("Serialized size: {} bytes", bytes.len());
            
            // Verify serialized data is not empty
            assert!(!bytes.is_empty(), "Serialized data should not be empty");
            
            // Deserialize
            let recovered_proof = InnerProductProof::from_bytes(&bytes);
            
            match recovered_proof {
                Ok(recovered) => {
                    // Verify vector lengths
                    assert_eq!(proof.L_vec.len(), recovered.L_vec.len(), "L_vec length mismatch");
                    assert_eq!(proof.R_vec.len(), recovered.R_vec.len(), "R_vec length mismatch");
                    
                    // Verify vector contents
                    for (i, (orig, recov)) in proof.L_vec.iter().zip(recovered.L_vec.iter()).enumerate() {
                        assert_eq!(orig, recov, "Element {} of L_vec mismatch", i);
                    }
                    
                    for (i, (orig, recov)) in proof.R_vec.iter().zip(recovered.R_vec.iter()).enumerate() {
                        assert_eq!(orig, recov, "Element {} of R_vec mismatch", i);
                    }
                    
                    // Verify scalar values
                    assert_eq!(proof.a, recovered.a, "a value mismatch");
                    assert_eq!(proof.b, recovered.b, "b value mismatch");
                    assert_eq!(proof.g_value, recovered.g_value, "g_value mismatch");
                    assert_eq!(proof.h_value, recovered.h_value, "h_value mismatch");
                    
                    // Verify group elements
                    assert_eq!(proof.g_final, recovered.g_final, "g_final mismatch");
                    assert_eq!(proof.h_final, recovered.h_final, "h_final mismatch");
                    assert_eq!(proof.g_proof, recovered.g_proof, "g_proof mismatch");
                    assert_eq!(proof.h_proof, recovered.h_proof, "h_proof mismatch");
                    
                    // Verify Affine commitments
                    assert_eq!(proof.g_commit, recovered.g_commit, "g_commit mismatch");
                    assert_eq!(proof.h_commit, recovered.h_commit, "h_commit mismatch");
                    assert_eq!(proof.g_commit_original, recovered.g_commit_original, "g_commit_original mismatch");
                    assert_eq!(proof.h_commit_original, recovered.h_commit_original, "h_commit_original mismatch");
                    
                    // Verify serialization-deserialization consistency
                    let re_serialized = recovered.to_bytes();
                    assert_eq!(bytes, re_serialized, "Re-serialization result inconsistent");
                }
                Err(e) => {
                    panic!("Deserialization failed (size={}): {}", size, e);
                }
            }
        }
    }

    // Test serialization edge case: empty proof
    #[test]
    fn test_ipa_serialization_empty() {
        // Create zero-value Affine points
        let zero_affine = G1::zero().into_affine();
        
        let proof = InnerProductProof {
            L_vec: vec![],
            R_vec: vec![],
            a: ScalarField::zero(),
            b: ScalarField::zero(),
            g_final: G1::zero(),
            h_final: G1::zero(),
            // KZG related fields
            g_commit: zero_affine,
            h_commit: zero_affine,
            g_commit_original: zero_affine,
            h_commit_original: zero_affine,
            g_value: ScalarField::zero(),
            h_value: ScalarField::zero(),
            g_proof: G1::zero(),
            h_proof: G1::zero(),
        };
        
        let bytes = proof.to_bytes();
        assert!(!bytes.is_empty(), "Serialized data for empty proof should not be empty");
        
        let recovered = InnerProductProof::from_bytes(&bytes)
            .expect("Deserialization of empty proof should not fail");
        
        // Verify all fields
        assert_eq!(proof.L_vec.len(), recovered.L_vec.len(), "L_vec length mismatch");
        assert_eq!(proof.R_vec.len(), recovered.R_vec.len(), "R_vec length mismatch");
        
        // Verify scalar values
        assert_eq!(proof.a, recovered.a, "a value mismatch");
        assert_eq!(proof.b, recovered.b, "b value mismatch");
        assert_eq!(proof.g_value, recovered.g_value, "g_value mismatch");
        assert_eq!(proof.h_value, recovered.h_value, "h_value mismatch");
        
        // Verify group elements
        assert_eq!(proof.g_final, recovered.g_final, "g_final mismatch");
        assert_eq!(proof.h_final, recovered.h_final, "h_final mismatch");
        assert_eq!(proof.g_proof, recovered.g_proof, "g_proof mismatch");
        assert_eq!(proof.h_proof, recovered.h_proof, "h_proof mismatch");
        
        // Verify Affine commitments
        assert_eq!(proof.g_commit, recovered.g_commit, "g_commit mismatch");
        assert_eq!(proof.h_commit, recovered.h_commit, "h_commit mismatch");
        assert_eq!(proof.g_commit_original, recovered.g_commit_original, "g_commit_original mismatch");
        assert_eq!(proof.h_commit_original, recovered.h_commit_original, "h_commit_original mismatch");
        
        // Verify vectors are indeed empty
        assert!(recovered.L_vec.is_empty(), "Deserialized L_vec should be empty");
        assert!(recovered.R_vec.is_empty(), "Deserialized R_vec should be empty");
        
        // Verify zero values
        assert!(recovered.a.is_zero(), "Deserialized a should be zero");
        assert!(recovered.b.is_zero(), "Deserialized b should be zero");
        assert!(recovered.g_value.is_zero(), "Deserialized g_value should be zero");
        assert!(recovered.h_value.is_zero(), "Deserialized h_value should be zero");
        assert!(recovered.g_final.is_zero(), "Deserialized g_final should be zero");
        assert!(recovered.h_final.is_zero(), "Deserialized h_final should be zero");
        assert!(recovered.g_proof.is_zero(), "Deserialized g_proof should be zero");
        assert!(recovered.h_proof.is_zero(), "Deserialized h_proof should be zero");
        
        // Verify serialization-deserialization consistency
        let re_serialized = recovered.to_bytes();
        assert_eq!(bytes, re_serialized, "Re-serialization result inconsistent");
    }

    // Test serialization error case: wrong byte length
    #[test]
    fn test_ipa_serialization_invalid_length() {
        let bytes = vec![0u8; 31]; // Not a multiple of 32
        let result = InnerProductProof::from_bytes(&bytes);
        assert!(result.is_err());
    }

    // Test serialization error case: invalid byte data
    #[test]
    fn test_ipa_serialization_invalid_data() {
        let mut bytes = vec![0u8; 64]; // Length for two points
        
        // Set first point to invalid compressed point representation
        bytes[0] = 0xff; // Invalid flag
        
        let result = InnerProductProof::from_bytes(&bytes);
        assert!(result.is_err());
    }

    // Test serialization error case: insufficient data
    #[test]
    fn test_ipa_serialization_insufficient_data() {
        // Create minimal valid proof (empty vectors)
        let proof = InnerProductProof {
            L_vec: vec![],
            R_vec: vec![],
            a: ScalarField::zero(),
            b: ScalarField::zero(),
            g_final: G1::zero(),
            h_final: G1::zero(),
            g_commit: G1::zero().into_affine(),
            h_commit: G1::zero().into_affine(),
            g_commit_original: G1::zero().into_affine(),
            h_commit_original: G1::zero().into_affine(),
            g_value: ScalarField::zero(),
            h_value: ScalarField::zero(),
            g_proof: G1::zero(),
            h_proof: G1::zero(),
        };
        
        let bytes = proof.to_bytes();
        
        // Test truncated data
        for i in 0..bytes.len() {
            let truncated = &bytes[0..i];
            let result = InnerProductProof::from_bytes(truncated);
            assert!(result.is_err(), "Truncated data should cause deserialization failure");
        }
    }

    // Test serialized size calculation
    #[test]
    fn test_ipa_serialized_size() {
        let mut rng = test_rng();
        for size in [0, 1, 4, 8, 16] {
            let proof = InnerProductProof {
                L_vec: random_g1_vec(&mut rng, size),
                R_vec: random_g1_vec(&mut rng, size),
                a: ScalarField::rand(&mut rng),
                b: ScalarField::rand(&mut rng),
                g_final: G1::rand(&mut rng),
                h_final: G1::rand(&mut rng),
                g_commit: G1::zero().into_affine(),
                h_commit: G1::zero().into_affine(),
                g_commit_original: G1::zero().into_affine(),
                h_commit_original: G1::zero().into_affine(),
                g_value: ScalarField::rand(&mut rng),
                h_value: ScalarField::rand(&mut rng),
                g_proof: G1::rand(&mut rng),
                h_proof: G1::rand(&mut rng),
            };
            
            let expected_size = proof.serialized_size();
            let actual_size = proof.to_bytes().len();
            
            assert_eq!(expected_size, actual_size,
                "serialized_size() returns value inconsistent with actual serialized size (size={})", size);
        }
    }
}