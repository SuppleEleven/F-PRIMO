use ark_bn254::{Fr, G1Projective as G1, G2Projective as G2};
use ark_ec::{pairing::Pairing, AffineRepr, CurveGroup, Group};
use ark_poly::{DenseUVPolynomial, univariate::DensePolynomial};
use ark_std::{rand::Rng, ops::Mul, UniformRand};
use ark_ff::{Field, PrimeField, Zero, One};
use ark_bn254::Bn254;
use rand::RngCore;
use rayon::prelude::*;

type VecFr = Vec<Fr>;
type PolyFr = DensePolynomial<Fr>;
type CommitmentG1 = <Bn254 as Pairing>::G1Affine;
type CommitmentGt = <Bn254 as Pairing>::G2Affine;

use crate::kzg::*;
use crate::random_scalar;
use crate::utils::*;

use rand::thread_rng;
use std::cell::RefCell;
use std::sync::Mutex;
use lazy_static::lazy_static;

thread_local! {
    static THREAD_RNG: RefCell<rand::rngs::ThreadRng> = RefCell::new(thread_rng());
}

pub fn prover_part1<R: RngCore>(
    rng: &mut R,
    kzg: &KZG,
    W_L: VecFr,  // left input constraint matrix vector
    W_R: VecFr,  // right input constraint matrix vector
    W_O: VecFr,  // output constraint matrix vector
    W_U: VecFr,  // fourth constraint matrix vector (PLONK extension)
    c: VecFr,    // public input vector
    I: Vec<usize>,  // copy constraint index set
    mapping: &MultiVectorMapping,  // multiplication constraint index set
    a_L: VecFr,  // left witness vector
    a_R: VecFr,  // right witness vector
    a_O: VecFr,  // output witness vector
    u: VecFr,    // fourth witness vector (PLONK extension)
) -> (
    CommitmentG1,
    CommitmentG1, 
    CommitmentG1, 
    VecFr,       
    VecFr,       
    usize,        
    Fr,
    Fr,
    Fr,
) {
    let n = a_L.len();  // circuit size / number of constraints
    assert_eq!(n, W_L.len(), "W_L length does not match a_L");
    assert_eq!(n, W_R.len(), "W_R length does not match a_L");
    assert_eq!(n, W_O.len(), "W_O length does not match a_L");
    let N = n;
    let r1 = Fr::rand(rng);
    let r2 = Fr::rand(rng);
    let r3 = Fr::rand(rng);
    let K_L: VecFr = (0..n).map(|_| Fr::rand(rng)).collect();
    let K_R: VecFr = (0..n).map(|_| Fr::rand(rng)).collect();

    let ((A_I_sum, A_O_sum), K_sum) = rayon::join(
        || {
            rayon::join(
                || {
                    (0..n).into_par_iter()
                        .map(|i| kzg.srs.g1[i] * (a_L[i]) + kzg.srs.g1[N + 1 + i] * (a_R[i]))
                        .reduce(|| G1::zero(), |a, b| a + b)
                },
                || {
                    (0..n).into_par_iter()
                        .map(|i| kzg.srs.g1[i] * (a_O[i]))
                        .reduce(|| G1::zero(), |a, b| a + b)
                }
            )
        },
        || {
            (0..n).into_par_iter()
                .map(|i| kzg.srs.g1[i] * (K_L[i]) + kzg.srs.g1[N + 1 + i] * (K_R[i]))
                .reduce(|| G1::zero(), |a, b| a + b)
        }
    );
   
    let A_I = kzg.srs.g1[N] * (r1) + A_I_sum;
    let A_O = kzg.srs.g1[N] * (r2) + A_O_sum;
    let K = kzg.srs.g1[N] * (r3) + K_sum;

    (
        A_I.into_affine(),  // convert to affine coordinates
        A_O.into_affine(),
        K.into_affine(),
        K_L,
        K_R,
        n,
        r1,
        r2,
        r3,
    )
}

/// Verifier variant: sample evaluation point `beta` and send to prover, receive (value, proof) pair then use KZG verification
/// These openings ensure that the outsourced group elements are correctly formatted. Return the sampled `beta` so that the caller can request openings at that point from the prover.
pub fn verifier_sample_beta<R: RngCore>(rng: &mut R) -> Fr {
    Fr::rand(rng)
}

pub fn verifier_part1<R: RngCore>(
    rng: &mut R,
    kzg: &KZG,
    W_L: VecFr, 
    W_R: VecFr, 
    W_O: VecFr, 
    W_U: VecFr,  
    c: VecFr, 
    I: Vec<usize>,  
    mapping: &MultiVectorMapping, 
    A_I: CommitmentG1,
    A_O: CommitmentG1,
    K: CommitmentG1,
) -> (Fr, Fr){
    // Generate challenges using Fiat-Shamir transform (should be based on hash of commitments)
    let y = Fr::rand(rng);  // linearization polynomial challenge
    let z = Fr::rand(rng);  // copy constraint challenge
    (y, z)
}

pub fn prover_part2<R: RngCore>(
    rng: &mut R,
    kzg: &KZG,
    values: &[Vec<Fr>],
    W_L: VecFr,  
    W_R: VecFr, 
    W_O: VecFr, 
    W_U: VecFr,  
    c: VecFr,      
    I: Vec<usize>, 
    mapping: &MultiVectorMapping,  
    a_L: VecFr,  
    a_R: VecFr,  
    a_O: VecFr,  
    u: VecFr,    
    A_I: CommitmentG1,
    A_O: CommitmentG1,
    K: CommitmentG1,
    K_L: VecFr,
    K_R: VecFr,
    y: Fr,               
    z: Fr,               
    r1: Fr,
    r2: Fr,
    r3: Fr,
    l: usize,                   
    m_per_vector: Vec<usize>, 
    r_q: Vec<Fr>,         
) -> (
    Vec<CommitmentG1>, 
    CommitmentG1, 
    Vec<Vec<Fr>>,
    Vec<Vec<Fr>>,
    VecFr,
    VecFr,
    VecFr,
    VecFr,
) {
    // Compute y^n and y^{-n}
    let n = a_L.len(); 
    let Q = W_L.len(); 
    let y_inv = y.inverse().expect("y cannot be zero, the protocol ensures challenge is nonzero");
    let ((y_pow_n, y_inv_pow_n), z_pow_Q_plus_1): ((Vec<Fr>, Vec<Fr>), Vec<Fr>) = rayon::join(
        || {
            // Inner parallel: compute y_pow_n and y_inv_pow_n simultaneously
            rayon::join(
                || (0..n).into_par_iter().map(|i| y.pow([i as u64])).collect::<Vec<Fr>>(),
                || (0..n).into_par_iter().map(|i| y_inv.pow([i as u64])).collect::<Vec<Fr>>()
            )
        },
        || {
            // Construct z_{[1:]}^{Q+1} (z to powers 1..Q)
            (0..Q).into_par_iter().map(|i| z.pow([(i+1) as u64])).collect::<Vec<Fr>>()
        }
    );

    let (term_left, term_right): (VecFr, VecFr) = rayon::join(
        || {
            // Compute δ(y, z) = <y^{-n} ◦ (z^{Q+1} · W_R), z^{Q+1} · W_L>
            (0..n.min(Q)).into_par_iter().map(|i| y_inv_pow_n[i] * (z_pow_Q_plus_1[i] * W_R[i])).collect::<VecFr>()
        },
        || {
            // Compute z^{Q+1} · W_L (element-wise multiplication)
            (0..Q).into_par_iter().map(|i| z_pow_Q_plus_1[i] * W_L[i]).collect::<VecFr>()
        }
    );

    // Inner product <term_left, term_right> (ensure length compatibility as per protocol)
    let delta = inner_product(&term_left, &term_right);

    let (l_poly_coeffs, r_poly_coeffs) = rayon::join(
        || {
            // l(X) = a_L·X + a_O·X² + y^{-n}◦(z^{Q+1}·W_R)·X + K_L·X³
            let mut l_poly_coeffs = vec![vec![Fr::zero(); n]; 4]; // 4 coefficients, each a vector of length n
            
            // 1. X^1 coefficient ———— a_L
            l_poly_coeffs[1] = a_L.clone();
            
            // X^1 coefficient ————  y^{-n}◦(z^{Q+1}·W_R)
            let y_z_W_R: Vec<Fr> = (0..n).into_par_iter()
                .map(|i| {
                    if i < Q {
                        y_inv_pow_n[i] * (z_pow_Q_plus_1[i] * W_R[i])
                    } else {
                        Fr::zero()
                    }
                })
                .collect();
            
            l_poly_coeffs[1] = (0..n).into_par_iter()
                .map(|i| l_poly_coeffs[1][i] + y_z_W_R[i])
                .collect();
 
            // 2. X^2 coefficient ———— a_O
            l_poly_coeffs[2] = a_O.clone();
            
            // 3. X^3 coefficient ———— K_L
            l_poly_coeffs[3] = K_L.clone();
            
            l_poly_coeffs
        },
        || {
            // r(X) = y^n◦a_R·X - y^n + z^{Q+1}◦(W_L·X + W_O) + y^n◦K_R·X³
            let mut r_poly_coeffs = vec![vec![Fr::zero(); n]; 4];
            
            // 1. X^0 coefficient ———— -y^n + z^{Q+1}◦W_O
            r_poly_coeffs[0] = (0..n).into_par_iter()
                .map(|i| {
                    let mut val = -y_pow_n[i];
                    if i < Q {
                        val = val + z_pow_Q_plus_1[i] * W_O[i];
                    }
                    val
                })
                .collect();
            
            // 2. X^1 coefficient ———— y^n◦a_R·X; X^1 coefficient ———— z^{Q+1}◦W_L·X 
            r_poly_coeffs[1] = (0..n).into_par_iter()
                .map(|i| {
                    let mut val = y_pow_n[i] * a_R[i];
                    if i < Q {
                        val = val + z_pow_Q_plus_1[i] * W_L[i];
                    }
                    val
                })
                .collect();
            
            // 3. X^3 coefficient ———— y^n◦K_R
            r_poly_coeffs[3] = (0..n).into_par_iter()
                .map(|i| y_pow_n[i] * K_R[i])
                .collect();
            
            r_poly_coeffs
        }
    );

    // Compute coefficients t_i of t(X) = <l(X), r(X)>
    let t_coeffs = vector_poly_inner_product(&l_poly_coeffs, &r_poly_coeffs);

    let (z_w, (a_L_a_R_y_n, a_O_y_n)): (Fr, (Fr, Fr))  = rayon::join(
        || {
            // w = W_L·a_L + W_R·a_R + W_O·a_O
            let w: VecFr = (0..Q).into_par_iter()
                .map(|i| W_L[i] * a_L[i % n] + W_R[i] * a_R[i % n] + W_O[i] * a_O[i % n])
                .collect();
            inner_product(&z_pow_Q_plus_1, &w) // extend w to length Q for inner product (protocol must confirm)
        },
        || {
            rayon::join(
                || {
                    // t_2 = <a_L, a_R ◦ y_n> - <a_O , y_n> + <z^{Q+1} , w> + δ(y, z)
                    let a_R_y_n: VecFr = a_R.par_iter().zip(y_pow_n.par_iter())
                        .map(|(&a_r, &y_pow)| a_r * (y_pow))
                        .collect();
                    inner_product(&a_L, &a_R_y_n)
                },
                || {
                    // let a_O_y_n = inner_product(&a_O, &y_pow_n);
                    inner_product(&a_O, &y_pow_n)
                }
            )
        }
    );
    
    let t_2 = a_L_a_R_y_n - a_O_y_n + z_w + delta;

    // Because RNG is not thread-safe, pre-generate all needed random numbers
    let indices = [1, 3, 4, 5, 6]; // polynomial degrees, not enum indices
    let mut precomputed_thetas: Vec<Fr> = Vec::new();
    for &i in &indices {
        if i < t_coeffs.len() {
            precomputed_thetas.push(Fr::rand(rng));
        }
    }
    let N = n;
    // Start verification timer
    let verification_start = std::time::Instant::now();
    let ((T_vec, theta_vec), pi_tilde): ((Vec<CommitmentG1>, Vec<Fr>), G1) = rayon::join(
        || {
            // Step 10: Construct [T_i]_T commitments
            let mut T_vec: Vec<CommitmentG1> = Vec::new();
            let mut theta_vec: Vec<Fr> = Vec::new();
            
            for (idx, &i) in indices.iter().enumerate() {
                if i < t_coeffs.len() {
                    let theta_i = precomputed_thetas[idx];
                    theta_vec.push(theta_i);
                    // [T_i]_T = [t_i · β^{N+1} + θ_i · β^{N+2}]_T
                    let T_i = (kzg.srs.g1[N + 1].mul(t_coeffs[i]) + kzg.srs.g1[N + 2].mul(theta_i)).into_affine();
                    T_vec.push(T_i);
                }
            }
            (T_vec, theta_vec)
        },
        || {
            // Construct [\tilde{\pi}]_1 aggregate proof
            let mut pi_tilde = G1::zero();
            
            // Compute powers of z: z^1, ..., z^{|I|}, used for linear combination
            let max_m = mapping.mappings.par_iter().map(|v| v.len()).max().unwrap_or(0);
            let z_pows: Vec<Fr> = (1..=max_m).into_par_iter().map(|j| z.pow([j as u64])).collect();
 
            // Compute s(q) values
            let s_q_values: Vec<usize> = (0..=l).into_par_iter().map(|q| mapping.s(q)).collect();
 
            for q in 0..l {
                let m_q = mapping.m_q(q);
                let mut pi_tilde_q = G1::zero(); // aggregate proof for this vector
                
                // Inner aggregation: Σ_{i=1}^{m_q} z^i · [π_{q,i}]_1
                for i in 0..m_q {
                    let exclude_start = start_exclude_timer();

                    let mapped_idx = mapping.get(q, i); // M(q,i)
                    
                    // Generate [π_{q,i}]_1 = [r_q · β^{2N+1-M(q,i)}]_1 
                    //                   + Σ_{j≠M(q,i)} [v_{q,j} · β^{N+1-M(q,i)+j}]_1
                    let mut pi_qi = G1::zero();
                    
                    // Part 1: r_q · β^{2N+1-M(q,i)}
                    if mapped_idx > 2 * N + 1 {
                        panic!("Index overflow: mapped_idx={} > 2*N+1={}", mapped_idx, 2 * N + 1);
                    }
                    let exp1 = 2 * N + 1 - mapped_idx;
                    pi_qi += kzg.srs.g1[exp1] * r_q[q];
                    
                    // Part 2: Σ_{j≠M(q,i)} [v_{q,j} · β^{N+1-M(q,i)+j}]_1
                    // Note: iterate over all elements of the original vector, not just the selected one
                    for (j, &v_qj) in values[q].iter().enumerate() {
                        if j != mapped_idx {
                            // Safety check: ensure index calculation does not overflow
                            if mapped_idx > N + 1 + j {
                                panic!("Index overflow: mapped_idx={} > N+1+j={}", mapped_idx, N + 1 + j);
                            }
                            let exp2 = N + 1 - mapped_idx + j;
                            pi_qi += kzg.srs.g1[exp2] * v_qj;
                        }
                    }
                    
                    stop_exclude_timer(exclude_start);
                    
                    // Multiply by z^i and accumulate (note: paper uses z^i, i starting from 1)
                    pi_tilde_q += pi_qi * z_pows[i];
                }
                
                // Outer aggregation: multiply by z^{s(q)} and add to total proof
                let z_s_q = z.pow([s_q_values[q] as u64]);
                pi_tilde += pi_tilde_q * z_s_q;
            }
            
            pi_tilde
        }
    );

    // End verification timer
    let verification_duration = verification_start.elapsed();
    println!("Excluded timing module - duration: {:.3} ms", verification_duration.as_millis() as f64);
    
        (T_vec, 
         pi_tilde.into_affine(),
         l_poly_coeffs,
         r_poly_coeffs,
         theta_vec,
         y_pow_n,
         y_inv_pow_n,
         z_pow_Q_plus_1,
        )
}

pub fn verifier_part2<R: RngCore>(
    rng: &mut R,
    kzg: &KZG,
    W_L: VecFr,  
    W_R: VecFr,  
    W_O: VecFr,  
    W_U: VecFr,  
    c: VecFr,    
    I: Vec<usize>,
    mapping: &MultiVectorMapping,  
    A_I: CommitmentG1,
    A_O: CommitmentG1,
    K: CommitmentG1,
    y: Fr,               
    z: Fr,              
    T_vec: Vec<CommitmentG1>, 
    pi_tilde: CommitmentG1, 
    n: usize,
) -> (Fr, Fr, VecFr, VecFr, VecFr) {
    // Compute y^n and y^{-n}
    let Q = W_L.len(); 
    let y_inv = y.inverse().expect("y cannot be zero, the protocol ensures challenge is nonzero");
    let ((y_pow_n, y_inv_pow_n), z_pow_Q_plus_1): ((Vec<Fr>, Vec<Fr>), Vec<Fr>) = rayon::join(
        || {
            // Inner parallel: compute y_pow_n and y_inv_pow_n simultaneously
            rayon::join(
                || (0..n).into_par_iter().map(|i| y.pow([i as u64])).collect::<Vec<Fr>>(),
                || (0..n).into_par_iter().map(|i| y_inv.pow([i as u64])).collect::<Vec<Fr>>()
            )
        },
        || {
            // Construct z_{[1:]}^{Q+1} (z to powers 1..Q)
            (0..Q).into_par_iter().map(|i| z.pow([(i+1) as u64])).collect::<Vec<Fr>>()
        }
    );
    
    let (term_left, term_right): (VecFr, VecFr) = rayon::join(
        || {
            // Compute δ(y, z) = <y^{-n} ◦ (z^{Q+1} · W_R), z^{Q+1} · W_L>
            (0..n.min(Q)).into_par_iter().map(|i| y_inv_pow_n[i] * (z_pow_Q_plus_1[i] * W_R[i])).collect::<VecFr>()
        },
        || {
            // Compute z^{Q+1} · W_L (element-wise multiplication)
            (0..Q).into_par_iter().map(|i| z_pow_Q_plus_1[i] * W_L[i]).collect::<VecFr>()
        }
    );

    // Inner product <term_left, term_right> (ensure length compatibility as per protocol)
    let delta = inner_product(&term_left, &term_right);

    let x = Fr::rand(rng);  
    (x, delta, 
     y_pow_n,
     y_inv_pow_n,
     z_pow_Q_plus_1,)
}

// Helper function: inner product of finite field vectors
fn inner_product(a: &VecFr, b: &VecFr) -> Fr {
    assert_eq!(a.len(), b.len(), "Vector lengths must match");
    a.iter()
        .zip(b.iter())
        .fold(Fr::zero(), |acc, (&x, &y)| acc + x * (y))
}

// Implement vector polynomial inner product
fn vector_poly_inner_product(l: &Vec<VecFr>, r: &Vec<VecFr>) -> Vec<Fr> {
    let degree = l.len() + r.len() - 2; // degree of resulting polynomial
    let mut result = vec![Fr::zero(); degree + 1];
    
    for (i, l_coeff) in l.iter().enumerate() {
        for (j, r_coeff) in r.iter().enumerate() {
            let ip = inner_product(l_coeff, r_coeff);
            result[i + j] = result[i + j] + ip;
        }
    }
    result
}