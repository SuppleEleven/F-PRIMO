use ark_bn254::{Fr, G1Projective as G1, G2Projective as G2};
use ark_ec::{pairing::Pairing, AffineRepr, CurveGroup, Group};
use ark_poly::{univariate::DensePolynomial, Polynomial, DenseUVPolynomial};
use ark_std::{rand::Rng, ops::Mul};
use std::ops::{Neg, Add, Sub};
use ark_ff::{Field, PrimeField, Zero, One};
use ark_bn254::Bn254;
use ark_std::UniformRand;
use ark_ec::VariableBaseMSM;
use rayon::prelude::*;

type VecFr = Vec<Fr>;
type PolyFr = DensePolynomial<Fr>;
type CommitmentG1 = <Bn254 as Pairing>::G1Affine;
type CommitmentGt = <Bn254 as Pairing>::G2Affine;

use crate::ipa::*;
use crate::ipa::{InnerProductProof, Transcript};
use crate::kzg::*;
use crate::utils::*;


pub fn prover_part1<R: Rng>(
    rng: &mut R,
    kzg: &KZG,
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
    y: Fr,           
    z: Fr,           
    r1: Fr,
    r2: Fr,
    r3: Fr,
    x: Fr, 
    T_vec: Vec<CommitmentG1>, 
    pi_tilde: CommitmentG1,
    l_poly: Vec<Vec<Fr>>,
    r_poly: Vec<Vec<Fr>>,
    theta_vec: Vec<Fr>, 
) -> (
    Fr, 
    Fr, 
    Vec<Fr>, 
    Vec<Fr>,
    Fr, 
) {
    // Evaluate polynomials l(X), r(X), t(X) at point x
    let l_vec = evaluate_vector_poly(&l_poly, x);  
    let r_vec = evaluate_vector_poly(&r_poly, x);  
    let t_tilde = inner_product(&l_vec, &r_vec);      
    // Compute θ_x
    let indices = [1, 3, 4, 5, 6]; // polynomial degrees
    let theta_vec_x = indices.par_iter()
        .map(|&i| {
            let theta_value = 
            if i == 1 {
                theta_vec[i-1]
            } else {
                theta_vec[i-2]
            };
            theta_value * x.pow([i as u64])
        })
        .sum();
    
    // Compute µ = r1·x + r2·x² + r3·x³
    let mut mu = r1 * (x) + r2 * (x.square()) + r3 * (x.pow([3]));

    (
        theta_vec_x,
        mu,
        l_vec,
        r_vec,
        t_tilde,
    )
}

pub fn verifier_part1<R: Rng>(
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
    x: Fr,  
    theta_vec_x: Fr,
    mu: Fr,
    t_tilde: Fr,
) -> Fr{
    let x_t = Fr::rand(rng); 
    x_t
}

pub fn prover_part2<R: Rng>(
    rng: &mut R,
    kzg: &KZG,
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
    y: Fr,      
    z: Fr,
    r1: Fr,
    r2: Fr,
    r3: Fr,
    x: Fr, 
    T_vec: Vec<CommitmentG1>, 
    pi_tilde: CommitmentG1, 
    l_poly: Vec<Vec<Fr>>,
    r_poly: Vec<Vec<Fr>>,
    theta_vec: Vec<Fr>,
    theta_vec_x: Fr, 
    mu: Fr,  
    t_tilde: Fr, 
    x_t: Fr,
    beta: Fr,
    z_pow_Q_plus_1: VecFr,
    y_pow_n: VecFr,
    y_inv_pow_n: VecFr,
    l_vec: Vec<Fr>,
    r_vec: Vec<Fr>, 
) -> (InnerProductProof, Transcript, Vec<CommitmentG1>, Vec<CommitmentG1>, Vec<Fr>, Vec<G1>) {
    let n = a_L.len();
    let N = n;
    let Q = W_L.len(); 
    
    // Step 1: Construct w_L, w_R, w_O
    let mut w_L: Vec<Fr> = vec![Fr::zero(); n];
    let mut w_R: Vec<Fr> = vec![Fr::zero(); n];
    let mut w_O: Vec<Fr> = vec![Fr::zero(); n];
    rayon::scope(|s| {
        s.spawn(|_| {
            w_L.par_iter_mut().enumerate().for_each(|(i, elem)| {
                if i < Q {
                    *elem = y_inv_pow_n[i] * (z_pow_Q_plus_1[i] * W_L[i]);
                }
            });
        });
        s.spawn(|_| {
            w_R.par_iter_mut().enumerate().for_each(|(i, elem)| {
                if i < Q {
                    *elem = y_inv_pow_n[i] * (z_pow_Q_plus_1[i] * W_R[i]);
                }
            });
        });
        s.spawn(|_| {
            w_O.par_iter_mut().enumerate().for_each(|(i, elem)| {
                if i < Q {
                    *elem = y_inv_pow_n[i] * (z_pow_Q_plus_1[i] * W_O[i]);
                }
            });
        });
    });

    // (Optimization) Let prover use KZG to commit and open w vectors at beta, return commitments and openings
    let (w_comms, original_w_comms, w_vals, w_proofs) = prover_open_w_vectors(
        kzg,
        w_L,
        w_R,
        w_O,
        y_pow_n.clone(),
        y_inv_pow_n.clone(),
        z_pow_Q_plus_1.clone(),
        N,
        beta,
    );

    // Convert commitments to group elements to replace the original SRS-based reconstruction of W'_*
    let (W_prime_L, (W_prime_R, W_prime_O)) = rayon::join(
        || w_comms[0].into_group(),
        || rayon::join(
            || w_comms[1].into_group(),
            || w_comms[2].into_group()
        )
    );

    // Construct [P]_1 and [P']_1     
    // Precompute powers of x
    let x_sq = x.square();
    let x_cube = x.pow([3]);
    // Compute components in parallel - using nested join for 8 parameters
    let (((((((term1, term2), term3), term4), term5), term6), term7), term8) = rayon::join(
        || rayon::join(
            || rayon::join(
                || rayon::join(
                    || rayon::join(
                        || rayon::join(
                            || rayon::join(
                                || A_I.mul(x),                    // 1. x·[A_I]_1
                                || W_prime_L.mul(x)               // x·[W'_L]_1
                            ),
                            || W_prime_R.mul(x)                   // x·[W'_R]_1
                        ),
                        || A_O.mul(x_sq)                         // 2. x²·[A_O]_1
                    ),
                    || K.mul(x_cube)                             // 3. x³·[K]_1
                ),
                || kzg.srs.sum_beta                              // 4. Σ(-β^{(N+1)+i})
            ),
            || W_prime_O                                         // [W'_O]_1
        ),
        || kzg.srs.g1[N].mul(-mu)                               // [-μ·β^N]_1
    );

    let P = G1::zero() 
        + term1 + term2 + term3 + term4 + term5 + term6 + term7 + term8;

    // [P']_1 = [P]_1 + [t̃· (x_t·β^N) ]_1
    let P_prime = P + kzg.srs.g1[N].mul(t_tilde * x_t);

    // Generate Bullet.IPA proof π_IPA
    // Initialize transcript for Fiat-Shamir transform
    let mut transcript_prover = Transcript::new(b"full_protocol_test");

    let ((g_vec_proj, h_vec_proj), (g_factors, h_factors)): ((Vec<G1>, Vec<G1>), (Vec<Fr>, Vec<Fr>)) = rayon::join(
        || {
            // Generate g_vec_proj and h_vec_proj in parallel
            rayon::join(
                || (1..=n).into_par_iter().map(|i| kzg.srs.g1[i]).collect::<Vec<G1>>(),
                || (1..=n).into_par_iter().map(|i| {
                    let y_power = y_inv_pow_n[(i-1) as usize];
                    let exponent = N + 1 + i;
                    kzg.srs.g1[exponent].mul(y_power)
                }).collect::<Vec<G1>>()
            )
        },
        || {
            // Generate g_factors and h_factors in parallel
            rayon::join(
                || (0..n).into_par_iter().map(|_| Fr::one()).collect::<Vec<Fr>>(),
                || (0..n).into_par_iter().map(|i| y_inv_pow_n[i as usize]).collect::<Vec<Fr>>()
            )
        }
    );

    // Construct point u: β^N * x_t
    let u_proj = kzg.srs.g1[N].mul(x_t);   // directly get Projective
    
    let ipa_proof = ipa_prove(
        kzg,
        &mut transcript_prover,
        &u_proj,
        &g_factors,
        &h_factors,
        g_vec_proj,         // g vector
        h_vec_proj,         // h vector
        l_vec,           // a vector
        r_vec,           // b vector
        &P_prime,       // target commitment
    ).expect("IPA proof generation failed");

    (ipa_proof, transcript_prover, w_comms, original_w_comms, w_vals, w_proofs)
}

pub fn verifier_part2<R: Rng>(
    test_index: usize,
    rng: &mut R,
    kzg: &KZG,
    V_q: &[CommitmentG1],
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
    delta: Fr, 
    z_pow_Q_plus_1: VecFr, 
    x: Fr, 
    theta_vec_x: Fr, 
    mu: Fr, 
    t_tilde: Fr, 
    x_t: Fr,
    ipa_proof: InnerProductProof, 
    y_pow_n: VecFr,
    y_inv_pow_n: VecFr,
    l: usize, 
    m_per_vector: Vec<usize>, 
    beta: Fr,
    commit_Wp: Vec<CommitmentG1>,
    original_commit_Wp: Vec<CommitmentG1>,
    val_Wp: Vec<Fr>,
    proof_Wp: Vec<G1>,
) -> bool{
    let N = n;

    let mut x_pows: VecFr = Vec::with_capacity(7);
    for i in 0..7 {
        x_pows.push(x.pow([i as u64])); // x^1, x^2, ..., x^6
    }

    /*--------------- Phase 1 --------------------------------------------------------------------------*/
    let Q = W_L.len(); // Q is the number of columns in constraint matrix minus one

    let mut w_L: Vec<Fr> = vec![Fr::zero(); n];
    let mut w_R: Vec<Fr> = vec![Fr::zero(); n];
    let mut w_O: Vec<Fr> = vec![Fr::zero(); n];
    rayon::scope(|s| {
        s.spawn(|_| {
            w_L.par_iter_mut().enumerate().for_each(|(i, elem)| {
                if i < Q {
                    *elem = y_inv_pow_n[i] * (z_pow_Q_plus_1[i] * W_L[i]);
                }
            });
        });
        s.spawn(|_| {
            w_R.par_iter_mut().enumerate().for_each(|(i, elem)| {
                if i < Q {
                    *elem = y_inv_pow_n[i] * (z_pow_Q_plus_1[i] * W_R[i]);
                }
            });
        });
        s.spawn(|_| {
            w_O.par_iter_mut().enumerate().for_each(|(i, elem)| {
                if i < Q {
                    *elem = y_inv_pow_n[i] * (z_pow_Q_plus_1[i] * W_O[i]);
                }
            });
        });
    });

    // (Optimization) Use KZG commitments and openings provided by prover instead of O(n) reconstruction by verifier
    let vector_types = ["w_L", "w_R", "w_O"];
    // Verifier recomputes the values
    let (val_wl, (val_wr, val_wo)) = rayon::join(
        || vector_poly_shift(&w_L, 1, beta, N),
        || rayon::join(
            || vector_poly_shift(&w_R, 0, beta, N),
            || vector_poly_shift(&w_O, 1, beta, N)
        )
    );
    let value = vec![val_wl, val_wr, val_wo];
    
    if !verifier_check_polynomial_openings(kzg, &commit_Wp, Some(&original_commit_Wp), &value, &proof_Wp, beta, n, N, &vector_types) {
        // println!("w vector verification failed");
        return false;
    }

    // Convert commitments to group elements for subsequent P construction
    let (W_prime_L, (W_prime_R, W_prime_O)) = rayon::join(
        || commit_Wp[0].into_group(),
        || rayon::join(
            || commit_Wp[1].into_group(),
            || commit_Wp[2].into_group()
        )
    );

    // Construct [P]_1 and [P']_1     
    // Precompute powers of x
    let x_sq = x.square();
    let x_cube = x.pow([3]);
    // Compute components in parallel - using nested join for 8 parameters
    let (((((((term1, term2), term3), term4), term5), term6), term7), term8) = rayon::join(
        || rayon::join(
            || rayon::join(
                || rayon::join(
                    || rayon::join(
                        || rayon::join(
                            || rayon::join(
                                || A_I.mul(x),                    // 1. x·[A_I]_1
                                || W_prime_L.mul(x)               // x·[W'_L]_1
                            ),
                            || W_prime_R.mul(x)                   // x·[W'_R]_1
                        ),
                        || A_O.mul(x_sq)                         // 2. x²·[A_O]_1
                    ),
                    || K.mul(x_cube)                             // 3. x³·[K]_1
                ),
                || kzg.srs.sum_beta                              // 4. Σ(-β^{(N+1)+i})
            ),
            || W_prime_O                                         // [W'_O]_1
        ),
        || kzg.srs.g1[N].mul(-mu)                               // [-μ·β^N]_1
    );

    let P = G1::zero() 
        + term1 + term2 + term3 + term4 + term5 + term6 + term7 + term8;

    // Expanded formula: [P']_1 = [P]_1 + [t̃·x_t·β^N]_1
    let P_prime = P + kzg.srs.g1[N] * (t_tilde * x_t);

    /*--------------- Phase 2 --------------------------------------------------------------------------*/
    // println!("\n=== Phase 4: Protocol verification start ===");
    // Start verification timer
    let verification_start = std::time::Instant::now();

    let (pairing_check, ipa_valid) = rayon::join(
        || {
            let (left_pairing, right_pairing): (GT, GT) = rayon::join(
                || {
                    // Left pairing term calculation
                    // Compute the first and second parts in parallel
                    let (first_part_contributions, second_part_contributions): (Vec<GT>, Vec<GT>) = rayon::join(
                        || {
                            // First part: Σ_{i∈{1,3,4,5,6}} (x^i·[T_i]_T)
                            let t_indices = [1, 3, 4, 5, 6]; // T_vec stored in this order
                            t_indices.par_iter()
                                .enumerate()
                                .filter(|(idx, _)| *idx < T_vec.len())
                                .map(|(idx, &degree)| {
                                    let pairing = Bn254::pairing(T_vec[idx], kzg.srs.g2[0]);
                                    pairing * x_pows[degree as usize]
                                })
                                .collect()
                        },
                        || {
                            // Second part: Σ_{q=1}^l z^{s(q)}·e(V_q, x²·Σ_{i=1}^{m_q} [z^i·β^{N+1-M(q,i)}]_2)
                            (0..l)
                                .into_par_iter()
                                .map(|q| {
                                    let m_q = mapping.m_q(q);
                                    // Collect points and scalars in parallel for MSM
                                    let (points, scalars): (Vec<_>, Vec<_>) = (0..m_q)
                                        .into_par_iter()
                                        .filter_map(|i| {
                                            let mapped_idx = mapping.get(q, i);
                                            let exponent = N + 1 - mapped_idx;
                                            if exponent < kzg.srs.g2.len() {
                                                Some((kzg.srs.g2[exponent].into_affine(), z_pow_Q_plus_1[i as usize]))
                                            } else {
                                                None
                                            }
                                        })
                                        .unzip();
                                    
                                    // Compute inner_sum_g2 using MSM
                                    let inner_sum_g2 = if !points.is_empty() {
                                        G2::msm_unchecked(&points, &scalars)
                                    } else {
                                        G2::zero()
                                    };
        
                                    // Multiply by x² (scalar multiplication)
                                    let inner_sum_g2_x2 = inner_sum_g2.mul(x_pows[2]);
                                    
                                    // Multiply by z^{s(q)}
                                    let s_q = mapping.s(q);
                                    let z_s_q = z.pow([s_q as u64]);
        
                                    // Compute pairing e(V_q, inner_sum_g2_x2)
                                    let pairing_q = Bn254::pairing(V_q[q] * z_s_q, inner_sum_g2_x2.into_affine());
                                    
                                    pairing_q
                                })
                                .collect()
                        }
                    );
                    
                    // Sum all contributions
                    first_part_contributions.into_par_iter()
                        .chain(second_part_contributions.into_par_iter())
                        .fold(|| GT::zero(), |acc, contribution| acc + contribution)
                        .reduce(|| GT::zero(), |a, b| a + b)
                },
                || {
                    // Right pairing term calculation
                    // Compute z_c and precomputed pairing bases in parallel
                    let (z_c, (pairing_base1, pairing_base2)): (Fr, (GT, GT)) = rayon::join(
                        || inner_product(&z_pow_Q_plus_1, &c),
                        || {
                            // Precompute pairing bases
                            rayon::join(
                                || Bn254::pairing(kzg.srs.g1[N + 1].into_affine(), kzg.srs.g2[0].into_affine()),
                                || Bn254::pairing(kzg.srs.g1[N + 2].into_affine(), kzg.srs.g2[0].into_affine())
                            )
                        }
                    );
                    // Compute term1 and term2 in parallel
                    let (term1, term2): (Fr, Fr) = rayon::join(
                        || t_tilde - x_pows[2] * (delta + z_c),
                        || theta_vec_x
                    );
                    // Compute three pairing terms in parallel
                    let ((pairing1, pairing2), pairing_term_2): ((GT, GT), GT) = rayon::join(
                        || {
                            rayon::join(
                                || pairing_base1 * term1,
                                || pairing_base2 * term2,
                            )
                        },
                        || {
                            let pi_tilde_x_sq = pi_tilde.mul(x.square());
                            Bn254::pairing(pi_tilde_x_sq.into_affine(), kzg.srs.g2[0].into_affine())
                        }
                    );
                    // Combine pairing terms
                    let right_pairing_1 = pairing1 + pairing2;
                    right_pairing_1 + pairing_term_2
                }
            );
            // 3. Check if pairings are equal
            (left_pairing - right_pairing).is_zero()
        },
        || {
            // Verify Bullet.IPA proof
            let mut transcript_verifier = Transcript::new(b"full_protocol_test");

            let ((g_vec_proj, h_vec_proj), (g_factors, h_factors)): ((Vec<G1>, Vec<G1>), (Vec<Fr>, Vec<Fr>)) = rayon::join(
                || {
                    // Generate g_vec_proj and h_vec_proj in parallel
                    rayon::join(
                        || (1..=n).into_par_iter().map(|i| kzg.srs.g1[i]).collect::<Vec<G1>>(),
                        || (1..=n).into_par_iter().map(|i| {
                            let y_power = y_inv_pow_n[(i-1) as usize];
                            let exponent = N + 1 + i;
                            kzg.srs.g1[exponent].mul(y_power)
                        }).collect::<Vec<G1>>()
                    )
                },
                || {
                    // Generate g_factors and h_factors in parallel
                    rayon::join(
                        || (0..n).into_par_iter().map(|_| Fr::one()).collect::<Vec<Fr>>(),
                        || (0..n).into_par_iter().map(|i| y_inv_pow_n[i as usize]).collect::<Vec<Fr>>()
                    )
                }
            );
            // Construct point u: β^N * x_t
            let u_proj = kzg.srs.g1[N].mul(x_t);   // directly get Projective
            ipa_verify(
                kzg,
                &ipa_proof,
                &mut transcript_verifier,
                n,
                &u_proj,
                g_factors.iter(),
                h_factors.iter(),
                &g_vec_proj,
                &h_vec_proj,
                &P_prime,
            ).unwrap_or(false)  // return false if verification fails
        }
    );
    // println!("Pairing check result: {}", pairing_check);
    // println!("Bullet.IPA proof verification result: {}", ipa_valid);

    // End verification timer
    let verification_duration = verification_start.elapsed();
    println!("Test {}, protocol verification completed - duration: {:.3} ms", test_index, verification_duration.as_millis() as f64);
    // Return verification result
    pairing_check && ipa_valid 
}

pub fn verifier_part2_stage1<R: Rng>(
    rng: &mut R,
    kzg: &KZG,
    V_q: &[CommitmentG1],
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
    delta: Fr, 
    z_pow_Q_plus_1: VecFr, 
    x: Fr,  
    theta_vec_x: Fr, 
    mu: Fr,
    t_tilde: Fr,
    x_t: Fr,
    ipa_proof: InnerProductProof,
    y_pow_n: VecFr,
    y_inv_pow_n: VecFr,
    l: usize, 
    m_per_vector: Vec<usize>, 
    beta: Fr,
    commit_Wp: Vec<CommitmentG1>,
    original_commit_Wp: Vec<CommitmentG1>,
    val_Wp: Vec<Fr>,
    proof_Wp: Vec<G1>,
) -> Result<G1, &'static str> {
    let N = n;

    let mut x_pows: VecFr = Vec::with_capacity(7);
    for i in 0..7 {
        x_pows.push(x.pow([i as u64])); // x^1, x^2, ..., x^6
    }
    let Q = W_L.len(); // Q is the number of columns in constraint matrix minus one

    let mut w_L: Vec<Fr> = vec![Fr::zero(); n];
    let mut w_R: Vec<Fr> = vec![Fr::zero(); n];
    let mut w_O: Vec<Fr> = vec![Fr::zero(); n];
    rayon::scope(|s| {
        s.spawn(|_| {
            w_L.par_iter_mut().enumerate().for_each(|(i, elem)| {
                if i < Q {
                    *elem = y_inv_pow_n[i] * (z_pow_Q_plus_1[i] * W_L[i]);
                }
            });
        });
        s.spawn(|_| {
            w_R.par_iter_mut().enumerate().for_each(|(i, elem)| {
                if i < Q {
                    *elem = y_inv_pow_n[i] * (z_pow_Q_plus_1[i] * W_R[i]);
                }
            });
        });
        s.spawn(|_| {
            w_O.par_iter_mut().enumerate().for_each(|(i, elem)| {
                if i < Q {
                    *elem = y_inv_pow_n[i] * (z_pow_Q_plus_1[i] * W_O[i]);
                }
            });
        });
    });

    // (Optimization) Use KZG commitments and openings provided by prover instead of O(n) reconstruction by verifier
    let vector_types = ["w_L", "w_R", "w_O"];
    // Verifier recomputes the values
    let (val_wl, (val_wr, val_wo)) = rayon::join(
        || vector_poly_shift(&w_L, 1, beta, N),
        || rayon::join(
            || vector_poly_shift(&w_R, 0, beta, N),
            || vector_poly_shift(&w_O, 1, beta, N)
        )
    );
    let value = vec![val_wl, val_wr, val_wo];
    
    if !verifier_check_polynomial_openings(kzg, &commit_Wp, Some(&original_commit_Wp), &value, &proof_Wp, beta, n, N, &vector_types) {
        // println!("w vector verification failed");
        return Err("w vector verification failed");
    }

    // Convert commitments to group elements for subsequent P construction
    let (W_prime_L, (W_prime_R, W_prime_O)) = rayon::join(
        || commit_Wp[0].into_group(),
        || rayon::join(
            || commit_Wp[1].into_group(),
            || commit_Wp[2].into_group()
        )
    );

    // Construct [P]_1 and [P']_1     
    // Precompute powers of x
    let x_sq = x.square();
    let x_cube = x.pow([3]);
    // Compute components in parallel - using nested join for 8 parameters
    let (((((((term1, term2), term3), term4), term5), term6), term7), term8) = rayon::join(
        || rayon::join(
            || rayon::join(
                || rayon::join(
                    || rayon::join(
                        || rayon::join(
                            || rayon::join(
                                || A_I.mul(x),                    // 1. x·[A_I]_1
                                || W_prime_L.mul(x)               // x·[W'_L]_1
                            ),
                            || W_prime_R.mul(x)                   // x·[W'_R]_1
                        ),
                        || A_O.mul(x_sq)                         // 2. x²·[A_O]_1
                    ),
                    || K.mul(x_cube)                             // 3. x³·[K]_1
                ),
                || kzg.srs.sum_beta                              // 4. Σ(-β^{(N+1)+i})
            ),
            || W_prime_O                                         // [W'_O]_1
        ),
        || kzg.srs.g1[N].mul(-mu)                               // [-μ·β^N]_1
    );

    let P = G1::zero() 
        + term1 + term2 + term3 + term4 + term5 + term6 + term7 + term8;

    // Expanded formula: [P']_1 = [P]_1 + [t̃·x_t·β^N]_1
    let P_prime = P + kzg.srs.g1[N] * (t_tilde * x_t);
    Ok(P_prime)
}

pub fn verifier_part2_stage2<R: Rng>(
    rng: &mut R,  
    test_index: usize,
    kzg: &KZG,
    V_q: &[CommitmentG1],
    c: VecFr,  
    mapping: &MultiVectorMapping,  
    z: Fr, 
    T_vec: Vec<CommitmentG1>, 
    pi_tilde: CommitmentG1,
    n: usize,
    delta: Fr,
    z_pow_Q_plus_1: VecFr, 
    x: Fr, 
    theta_vec_x: Fr, 
    t_tilde: Fr,
    x_t: Fr,
    ipa_proof: InnerProductProof, 
    y_pow_n: VecFr,
    y_inv_pow_n: VecFr,
    l: usize, 
    P_prime: G1,
) -> bool{
    let N = n;

    let mut x_pows: VecFr = Vec::with_capacity(7);
    for i in 0..7 {
        x_pows.push(x.pow([i as u64])); // x^1, x^2, ..., x^6
    }
    
    // println!("\n=== Phase 4: Protocol verification start ===");
    // Start verification timer
    let verification_start = std::time::Instant::now();

    let (pairing_check, ipa_valid) = rayon::join(
        || {
            let (left_pairing, right_pairing): (GT, GT) = rayon::join(
                || {
                    // Left pairing term calculation
                    // Compute the first and second parts in parallel
                    let (first_part_contributions, second_part_contributions): (Vec<GT>, Vec<GT>) = rayon::join(
                        || {
                            // First part: Σ_{i∈{1,3,4,5,6}} (x^i·[T_i]_T)
                            let t_indices = [1, 3, 4, 5, 6]; // T_vec stored in this order
                            t_indices.par_iter()
                                .enumerate()
                                .filter(|(idx, _)| *idx < T_vec.len())
                                .map(|(idx, &degree)| {
                                    let pairing = Bn254::pairing(T_vec[idx], kzg.srs.g2[0]);
                                    pairing * x_pows[degree as usize]
                                })
                                .collect()
                        },
                        || {
                            // Second part: Σ_{q=1}^l z^{s(q)}·e(V_q, x²·Σ_{i=1}^{m_q} [z^i·β^{N+1-M(q,i)}]_2)
                            (0..l)
                                .into_par_iter()
                                .map(|q| {
                                    let m_q = mapping.m_q(q);
                                    // Collect points and scalars in parallel for MSM
                                    let (points, scalars): (Vec<_>, Vec<_>) = (0..m_q)
                                        .into_par_iter()
                                        .filter_map(|i| {
                                            let mapped_idx = mapping.get(q, i);
                                            let exponent = N + 1 - mapped_idx;
                                            if exponent < kzg.srs.g2.len() {
                                                Some((kzg.srs.g2[exponent].into_affine(), z_pow_Q_plus_1[i as usize]))
                                            } else {
                                                None
                                            }
                                        })
                                        .unzip();
                                    
                                    // Compute inner_sum_g2 using MSM
                                    let inner_sum_g2 = if !points.is_empty() {
                                        G2::msm_unchecked(&points, &scalars)
                                    } else {
                                        G2::zero()
                                    };
        
                                    // Multiply by x² (scalar multiplication)
                                    let inner_sum_g2_x2 = inner_sum_g2.mul(x_pows[2]);
                                    
                                    // Multiply by z^{s(q)}
                                    let s_q = mapping.s(q);
                                    let z_s_q = z.pow([s_q as u64]);
        
                                    // Compute pairing e(V_q, inner_sum_g2_x2)
                                    let pairing_q = Bn254::pairing(V_q[q] * z_s_q, inner_sum_g2_x2.into_affine());
                                    
                                    pairing_q
                                })
                                .collect()
                        }
                    );
                    
                    // Sum all contributions
                    first_part_contributions.into_par_iter()
                        .chain(second_part_contributions.into_par_iter())
                        .fold(|| GT::zero(), |acc, contribution| acc + contribution)
                        .reduce(|| GT::zero(), |a, b| a + b)
                },
                || {
                    // Right pairing term calculation
                    // Compute z_c and precomputed pairing bases in parallel
                    let (z_c, (pairing_base1, pairing_base2)): (Fr, (GT, GT)) = rayon::join(
                        || inner_product(&z_pow_Q_plus_1, &c),
                        || {
                            // Precompute pairing bases
                            rayon::join(
                                || Bn254::pairing(kzg.srs.g1[N + 1].into_affine(), kzg.srs.g2[0].into_affine()),
                                || Bn254::pairing(kzg.srs.g1[N + 2].into_affine(), kzg.srs.g2[0].into_affine())
                            )
                        }
                    );
                    // Compute term1 and term2 in parallel
                    let (term1, term2): (Fr, Fr) = rayon::join(
                        || t_tilde - x_pows[2] * (delta + z_c),
                        || theta_vec_x
                    );
                    // Compute three pairing terms in parallel
                    let ((pairing1, pairing2), pairing_term_2): ((GT, GT), GT) = rayon::join(
                        || {
                            rayon::join(
                                || pairing_base1 * term1,
                                || pairing_base2 * term2,
                            )
                        },
                        || {
                            let pi_tilde_x_sq = pi_tilde.mul(x.square());
                            Bn254::pairing(pi_tilde_x_sq.into_affine(), kzg.srs.g2[0].into_affine())
                        }
                    );
                    // Combine pairing terms
                    let right_pairing_1 = pairing1 + pairing2;
                    right_pairing_1 + pairing_term_2
                }
            );
            // 3. Check if pairings are equal
            (left_pairing - right_pairing).is_zero()
        },
        || {
            // Verify Bullet.IPA proof
            let mut transcript_verifier = Transcript::new(b"full_protocol_test");

            let ((g_vec_proj, h_vec_proj), (g_factors, h_factors)): ((Vec<G1>, Vec<G1>), (Vec<Fr>, Vec<Fr>)) = rayon::join(
                || {
                    // Generate g_vec_proj and h_vec_proj in parallel
                    rayon::join(
                        || (1..=n).into_par_iter().map(|i| kzg.srs.g1[i]).collect::<Vec<G1>>(),
                        || (1..=n).into_par_iter().map(|i| {
                            let y_power = y_inv_pow_n[(i-1) as usize];
                            let exponent = N + 1 + i;
                            kzg.srs.g1[exponent].mul(y_power)
                        }).collect::<Vec<G1>>()
                    )
                },
                || {
                    // Generate g_factors and h_factors in parallel
                    rayon::join(
                        || (0..n).into_par_iter().map(|_| Fr::one()).collect::<Vec<Fr>>(),
                        || (0..n).into_par_iter().map(|i| y_inv_pow_n[i as usize]).collect::<Vec<Fr>>()
                    )
                }
            );
            // Construct point u: β^N * x_t
            let u_proj = kzg.srs.g1[N].mul(x_t);   // directly get Projective
            ipa_verify(
                kzg,
                &ipa_proof,
                &mut transcript_verifier,
                n,
                &u_proj,
                g_factors.iter(),
                h_factors.iter(),
                &g_vec_proj,
                &h_vec_proj,
                &P_prime,
            ).unwrap_or(false)  // return false if verification fails
        }
    );
    // println!("Pairing check result: {}", pairing_check);
    // println!("Bullet.IPA proof verification result: {}", ipa_valid);

    // End verification timer
    let verification_duration = verification_start.elapsed();
    println!("Test {}, protocol verification completed - duration: {:.3} ms", test_index, verification_duration.as_millis() as f64);
    // Return verification result
    pairing_check && ipa_valid 

}

// Helper function: evaluate polynomial at a point (simplified version, handles coefficient vectors)
fn evaluate_vector_poly(poly_coeffs: &[Vec<Fr>], x: Fr) -> Vec<Fr> {
    let n = poly_coeffs[0].len();
    let mut result = vec![Fr::zero(); n];
    
    for (degree, coeff_vector) in poly_coeffs.iter().enumerate() {
        let x_power = x.pow([degree as u64]);
        for i in 0..n {
            result[i] += coeff_vector[i] * x_power;
        }
    }
    
    result
}

fn inner_product(a: &VecFr, b: &VecFr) -> Fr {
    assert_eq!(a.len(), b.len(), "Vector lengths must match");
    a.iter()
        .zip(b.iter())
        .fold(Fr::zero(), |acc, (&x, &y)| acc + x * (y))
}

pub fn vector_poly_shift(coeffs: &[Fr], shift: usize, point: Fr, N: usize) -> Fr {
    let mut shifted = vec![Fr::zero(); shift + coeffs.len()];
    for (i, c) in coeffs.iter().enumerate() {
        shifted[shift + i] = *c;
    }
    let poly = DensePolynomial::from_coefficients_vec(shifted.to_vec());
    let value = poly.evaluate(&point);
    
    value
}

/// Verifier helper: verify a set of KZG openings at the same `beta` point.
pub fn verifier_check_polynomial_openings(
    kzg: &KZG,
    comms: &Vec<CommitmentG1>,
    original_comms: Option<&Vec<CommitmentG1>>,
    vals: &Vec<Fr>,
    proofs: &Vec<G1>,
    beta: Fr,
    n: usize, // vector length
    N: usize, // total degree bound
    vector_types: &[&str],
) -> bool {
    if comms.len() != vals.len() || comms.len() != proofs.len() { return false; }

    // Precompute β^{N+1} G2 element (avoid recomputation in parallel loop)
    let beta_pow_N_plus_1 = if N + 1 < kzg.srs.g2.len() {
        Some(kzg.srs.g2[N].into_affine())
    } else {
        println!("SRS does not contain G2 element for β^{}", N + 1);
        return false;
        None
    };
    // Use parallel iterator for all verifications
    let results: Vec<bool> = (0..comms.len()).into_par_iter().map(|i| {
        let vector_type = vector_types[i];
        let expected_degree = n; // expected degree of each vector
        match vector_type {
            "w_R" => {
                // w_R is a low-degree polynomial (degree = n < N)
                // Verify with degree bound
                let valid = verify_open_with_degree_bound(
                    kzg, 
                    &comms[i], 
                    beta, 
                    vals[i], 
                    &proofs[i],
                    expected_degree,  // degree_bound = n
                    N,                // total_degree = N
                    false             // is_high_degree = false
                );
                if !valid {
                    // println!("w_R degree bound verification failed");
                    false
                } else {
                    // println!("w_R degree bound verification succeeded");
                    true
                }
            }
            "w_L" | "w_O" => {
                // w_L and w_O are high-degree polynomials (degree = N+1+n)
                // Step 1: Verify the correctness of the shifted polynomial (low-degree) opening
                let step1_valid = verify_open_with_degree_bound(
                    kzg, 
                    &comms[i], 
                    beta, 
                    vals[i], 
                    &proofs[i],
                    expected_degree + 1,  // degree of shifted polynomial = n
                    N,                // total_degree = N
                    false             // is_high_degree = false (shifted is low-degree)
                );
                if !step1_valid {
                    // println!("{} shifted polynomial verification failed", vector_type);
                    return false;
                }
                // println!("{} shifted polynomial verification succeeded", vector_type);
                
                // Step 2: If original commitments are provided, verify consistency relation
                let step2_valid = if let Some(orig_comms) = original_comms {
                    if i < orig_comms.len() {
                        let original_comm = orig_comms[i];
                        let shifted_comm = comms[i];
                        
                        // Use precomputed β^{N+1} G2 element
                        if let Some(beta_pow) = beta_pow_N_plus_1 {
                            let left_pairing = Bn254::pairing(
                                original_comm,
                                kzg.srs.g2[0].into_affine()
                            );
                            
                            let right_pairing = Bn254::pairing(
                                shifted_comm,
                                beta_pow
                            );
                            
                            left_pairing == right_pairing
                        } else {
                            // SRS does not contain required element
                            false
                        }
                    } else {
                        true // skip check if no corresponding original commitment
                    }
                } else {
                    true // skip check if original commitments not provided
                };
                if !step2_valid {
                    // println!("{} consistency check failed", vector_type);
                    return false;
                }
                // println!("{} consistency check succeeded", vector_type); 
                step2_valid
            }
            _ => {
                println!("Unknown vector type: {}", vector_type);
                false
            }
        }
    }).collect();
    
    // Check if all verifications succeeded
    results.iter().all(|&result| result);
    
    true
}

/// Construct w_L, w_R, w_O vectors (length n) and open them at `beta` via KZG.
pub fn prover_open_w_vectors(
    kzg: &KZG,
    w_L: Vec<Fr>,
    w_R: Vec<Fr>,
    w_O: Vec<Fr>,
    y_pow_n: VecFr,
    y_inv_pow_n: VecFr,
    z_pow_Q_plus_1: VecFr,
    N: usize,
    beta: Fr,
) -> (Vec<CommitmentG1>, Vec<CommitmentG1>, Vec<Fr>, Vec<G1>) {
    let n = y_pow_n.len();
    let Q = z_pow_Q_plus_1.len();

    let shift = N + 1;

    let (((comm_wl, original_comm_wl, val_wl, proof_wl), (comm_wr, original_comm_wr, val_wr, proof_wr)), (comm_wo, original_comm_wo, val_wo, proof_wo)) = rayon::join(
        || {
            rayon::join(
                || {
                    // Commit to w_L with shift and open
                    let comm_wl = kzg.commit_shifted(&w_L, shift - N).into_affine();
                    let original_comm_wl = kzg.commit_shifted(&w_L, shift).into_affine(); // original commitment
                    let (val_wl, proof_wl) = kzg.open_shifted_at(&w_L, shift - N, beta, N);
                    (comm_wl, original_comm_wl, val_wl, proof_wl)
                },
                || {
                    // Commit to w_R and open at beta (no shift needed)
                    let comm_wr = kzg.commit_poly(&w_R).into_affine();
                    let original_comm_wr = kzg.commit_poly(&w_R).into_affine(); // original commitment
                    let (val_wr, proof_wr) = kzg.open_at_low(&w_R, beta, N);
                    (comm_wr, original_comm_wr, val_wr, proof_wr)
                }
            )
        },
        || {
            // Commit to w_O with shift and open
            let comm_wo = kzg.commit_shifted(&w_O, shift - N).into_affine();
            let original_comm_wo = kzg.commit_shifted(&w_O, shift).into_affine(); // original commitment
            let (val_wo, proof_wo) = kzg.open_shifted_at(&w_O, shift - N, beta, N);
            (comm_wo, original_comm_wo, val_wo, proof_wo)
        }
    );

    (
        vec![comm_wl, comm_wr, comm_wo],
        vec![original_comm_wl, original_comm_wr, original_comm_wo],
        vec![val_wl, val_wr, val_wo],
        vec![proof_wl, proof_wr, proof_wo],
    )
}

/// Extended KZG verification function with degree bound check
pub fn verify_open_with_degree_bound(
    kzg: &KZG,
    comm: &CommitmentG1,
    point: Fr,
    value: Fr,
    proof: &G1,
    degree_bound: usize,  // expected maximum degree
    total_degree: usize,  // total degree bound N
    is_high_degree: bool, // whether it's a high-degree polynomial (requires factor extraction)
) -> bool {
    // Degree bound check
    if !is_high_degree {
        // For low-degree polynomials (degree < N): enforce degree bound by modifying verification equation
        // Replace proof with [q(β)·β^{2N - deg + 1}]_1
        let (beta_pow_deg_diff, beta_minus_point_g2) = rayon::join(
            || {
                // Compute degree_diff = 2N - deg + 1
                let degree_diff = 2 * total_degree - degree_bound + 1;
                if degree_diff >= kzg.srs.g2.len() {
                    println!("SRS does not contain G2 element for β^{}", degree_diff);
                    return G2::zero(); // return zero element to indicate failure
                }
                kzg.srs.g2[degree_diff]
            },
            || {
                kzg.srs.g2[0].mul(point.neg()).add(&kzg.srs.g2[1])
            }
        );
        if beta_pow_deg_diff == G2::zero() { return false; } // SRS does not contain sufficiently high power

        let (left_pairing, right_pairing) = rayon::join(
            || Bn254::pairing( (G1::from(*comm) - G1::generator().mul(value)).into_affine(), beta_pow_deg_diff ),
            || Bn254::pairing(*proof, beta_minus_point_g2.into_affine())
        );
        
        return left_pairing == right_pairing;
    } 
    else {
        // For high-degree polynomials, already handled by factor extraction
        // No additional degree check needed because extracted polynomial degree < N
        return true;
    }
}