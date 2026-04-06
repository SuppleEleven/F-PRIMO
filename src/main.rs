use ark_std::rand::thread_rng;
use ark_std::UniformRand;
use ark_std::{rand::Rng, ops::Mul};
use std::ops::{Neg, Add, Sub};
use ark_bn254::Bn254;
use ark_poly::{univariate::DensePolynomial, Polynomial, DenseUVPolynomial};
use ark_bn254::{Fr, G1Projective as G1, G1Affine, G2Projective as G2};
use ark_ff::{Field, Zero, One, PrimeField};
use ark_ec::CurveGroup;
use ark_ec::pairing::Pairing;
use ark_serialize::CanonicalSerialize;
use sha2::{Sha256, Digest};
use rand::prelude::SliceRandom;
use std::time::{SystemTime, Duration};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Mutex;
use lazy_static::lazy_static;
use crate::utils::*;
use crate::kzg::*;
use rayon::prelude::*;
use std::sync::Arc;

type PolyFr = DensePolynomial<Fr>;
type CommitmentG1 = <Bn254 as Pairing>::G1Affine;
type CommitmentGt = <Bn254 as Pairing>::G2Affine;

mod part1;
mod part2;
mod ipa;
mod kzg;   
mod utils;

// Global thread pool configuration
lazy_static! {
    static ref THREAD_POOL: rayon::ThreadPool = rayon::ThreadPoolBuilder::new()
        .num_threads(num_cpus::get())
        .build()
        .unwrap();
}

// Modified main function with test options
fn main() {
    // Record program start time
    let start_time = std::time::Instant::now();
    println!("=== CP-ZKP-MS Protocol Test System ===");
    println!("1. Benchmark Tests");
    println!("2. Parameterized Tests");
    println!("3. Standard Commitment Test");
    println!("4. Delegated Commitment Test");
    println!("5. Proof Time Test");
    println!("6. Verification Time Test");
    println!("Select test mode:");

    let mut input = String::new();
    std::io::stdin().read_line(&mut input).expect("Failed to read input");

    let result = match input.trim() {
        "1" => {
            run_benchmark_tests()
        }
        "2" => {
            run_parameterized_tests()
        }
        "3" => {
            run_test_commitment()
        }
        "4" => {
            run_test_commitment_opt()
        }
        "5" => {
            run_parameterized_test_proof()
        }
        "6" => {
            run_parameterized_test_verify()
        }
        _ => {
            println!("Invalid selection, using benchmark tests");
            run_benchmark_tests()
        }
    };

    let actual_time = start_time.elapsed();
    println!("=== Test Completed ===");
    result
}

fn run_test_with_parameters(
    test_index: usize,
    n: usize, 
    m_per_vector: Vec<usize>, 
    l: usize,
    subset_ratio: usize,
    vector_len: usize,
    kzg: &KZG, 
) -> Result<Duration, String> {
    let test_start_time = std::time::Instant::now();
    
    if m_per_vector.len() != l {
        return Err(format!("m_per_vector长度{}与向量数量l={}不匹配", m_per_vector.len(), l));
    }
    for &m_q in &m_per_vector {
        if m_q > vector_len {
            return Err(format!("选择元素数{}大于向量长度{}", m_q, vector_len));
        }
    }

    // Create shared KZG instance
    let mut rng = thread_rng();

    let total_m: usize = m_per_vector.iter().sum(); 
    
    let degree = n * 8; // Max polynomial degree

    // Step 1: Generate test vectors
    let vectors: Vec<Vec<Fr>> = (0..l)
        .into_par_iter()
        .map(|q| {
            (0..vector_len)
                .map(|j| Fr::from((q as u64 + 1) * 1000 + j as u64))
                .collect()
        })
        .collect();

    // Step 2: Generate random blinding factors for each vector
    let r_q: Vec<Fr> = (0..l)
        .into_par_iter()
        .map_init(|| thread_rng(), |rng, _| Fr::rand(rng))
        .collect();

    // Step 3: Create commitments V_q for each vector
    let v_q_start = std::time::Instant::now();
    let V_q: Vec<G1> = (0..l)
        .into_iter()
        .map(|q| {
            let mut V = G1::zero();
            let N = n;
            V += kzg.srs.g1[N] * r_q[q];
            for j in 0..vectors[q].len() {
                V += kzg.srs.g1[j + 1] * vectors[q][j];
            }
            V
        })
        .collect();
    let v_q_duration = v_q_start.elapsed();
    println!(
        "Test {}: Vector commitments created - {} vectors, time: {:.3} ms",
        test_index,
        l,
        v_q_duration.as_millis() as f64
    );

    // Convert V_q to affine for verification
    let V_q_affine: Vec<_> = V_q.iter().map(|v| v.into_affine()).collect();

    // Step 4: Select elements and build M mapping
    let (mappings, selected_values): (Vec<Vec<usize>>, Vec<Fr>) = (0..l)
        .into_par_iter()
        .map(|q| {
            let mut available_indices: Vec<usize> = (0..vectors[q].len()).collect();
            available_indices.shuffle(&mut thread_rng());

            let mut M_q = Vec::new();
            let mut values = Vec::new();
            let max_count = m_per_vector[q].min(available_indices.len());

            for i in 0..max_count {
                let idx = available_indices[i];
                M_q.push(idx);
                values.push(vectors[q][idx]);
            }

            (M_q, values)
        })
        .fold(
            || (Vec::new(), Vec::new()),
            |(mut maps, mut vals), (map, val)| {
                maps.push(map);
                vals.extend(val);
                (maps, vals)
            }
        )
        .reduce(
            || (Vec::new(), Vec::new()),
            |(mut maps1, mut vals1), (maps2, vals2)| {
                maps1.extend(maps2);
                vals1.extend(vals2);
                (maps1, vals1)
            }
        );

    let mapping = MultiVectorMapping {
        mappings: mappings.clone(),
        vector_lengths: vectors.iter().map(|v| v.len()).collect(),
    };

    // Step 5: Build flattened index set I
    let I: Vec<usize> = (0..total_m).collect();
    // Step 6: Build flattened u vector (all selected values)
    let u: Vec<Fr> = selected_values;
    // Step 7: Convert 2D M mapping to 1D
    let M_flat: Vec<usize> = mappings.iter().flatten().cloned().collect();

    // Step 8: Create circuit witness (Hadamard product constraint: a_L ◦ a_R = a_O)
    let results: Vec<(Fr, Fr, Fr)> = (0..n)
        .into_par_iter()
        .map(|_| {
            let a_l = Fr::rand(&mut thread_rng());
            let a_r = Fr::rand(&mut thread_rng());
            let a_o = a_l * a_r;
            (a_l, a_r, a_o)
        })
        .collect();
    let (a_L, a_R, a_O): (Vec<Fr>, Vec<Fr>, Vec<Fr>) = results.into_iter().fold(
        (Vec::new(), Vec::new(), Vec::new()),
        |(mut a_l_vec, mut a_r_vec, mut a_o_vec), (a_l, a_r, a_o)| {
            a_l_vec.push(a_l);
            a_r_vec.push(a_r);
            a_o_vec.push(a_o);
            (a_l_vec, a_r_vec, a_o_vec)
        }
    );

    // Step 9: Create circuit constraint parameters
    let results: Vec<(Fr, Fr, Fr, Fr)> = (0..n)
        .into_par_iter()
        .map(|_| {
            let w_l = Fr::rand(&mut thread_rng());
            let w_r = Fr::rand(&mut thread_rng());
            let w_o = Fr::rand(&mut thread_rng());
            let w_u = Fr::rand(&mut thread_rng());
            (w_l, w_r, w_o, w_u)
        })
        .collect();
    let (W_L, W_R, W_O, W_U): (Vec<Fr>, Vec<Fr>, Vec<Fr>, Vec<Fr>) = results.into_iter().fold(
        (Vec::new(), Vec::new(), Vec::new(), Vec::new()),
        |(mut w_l_vec, mut w_r_vec, mut w_o_vec, mut w_u_vec), (w_l, w_r, w_o, w_u)| {
            w_l_vec.push(w_l);
            w_r_vec.push(w_r);
            w_o_vec.push(w_o);
            w_u_vec.push(w_u);
            (w_l_vec, w_r_vec, w_o_vec, w_u_vec)
        }
    );

    let c: Vec<Fr> = (0..n)
        .into_par_iter()
        .map(|i| {
            let left = W_L[i] * a_L[i] + W_R[i] * a_R[i] + W_O[i] * a_O[i];
            let w_u_u = if i < total_m { W_U[i] * u[i] } else { Fr::zero() };
            left - w_u_u
        })
        .collect();

    let mut pi_qi = Vec::new();
    for q in 0..l {
        let m_q = mapping.m_q(q);
        // Inner aggregation: Σ_{i=1}^{m_q} z^i · [π_{q,i}]_1
        for i in 0..m_q {
            let mapped_idx = mapping.get(q, i); // M(q,i)
            
            // Generate [π_{q,i}]_1 = [r_q · β^{2N+1-M(q,i)}]_1 
            //                   + Σ_{j≠M(q,i)} [v_{q,j} · β^{N+1-M(q,i)+j}]_1
            let mut pi_qiq = G1::zero();
            
            // Part 1: r_q · β^{2N+1-M(q,i)}
            if mapped_idx > 2 * n + 1 {
                panic!("Index overflow: mapped_idx={} > 2*N+1={}", mapped_idx, 2 * n + 1);
            }
            let exp1 = 2 * n + 1 - mapped_idx;
            pi_qiq += kzg.srs.g1[exp1] * r_q[q];
            
            // Part 2: Σ_{j≠M(q,i)} [v_{q,j} · β^{N+1-M(q,i)+j}]_1
            // Note: iterate over all elements of the original vector, not just the selected one
            for (j, &v_qj) in vectors[q].iter().enumerate() {
                if j != mapped_idx {
                    // Safety check: ensure index calculation does not overflow
                    if mapped_idx > n + 1 + j {
                        panic!("Index overflow: mapped_idx={} > N+1+j={}", mapped_idx, n + 1 + j);
                    }
                    let exp2 = n + 1 - mapped_idx + j;
                    pi_qiq += kzg.srs.g1[exp2] * v_qj;
                }
            }
            pi_qi.push(pi_qiq);
        }
    }

    // Protocol execution
    let beta = part1::verifier_sample_beta(&mut rng);

    let (A_I, A_O, K, K_L, K_R, n, r1, r2, r3) = part1::prover_part1(
        &mut rng,
        &kzg,
        W_L.clone(),
        W_R.clone(),
        W_O.clone(),
        W_U.clone(),
        c.clone(),
        I.clone(),
        &mapping,
        a_L.clone(),
        a_R.clone(),
        a_O.clone(),
        u.clone(),
    );

    let (y, z) = part1::verifier_part1(
        &mut rng,
        &kzg,
        W_L.clone(),
        W_R.clone(),
        W_O.clone(),
        W_U.clone(),
        c.clone(),
        I.clone(),
        &mapping,
        A_I,
        A_O,
        K,
    );

    let (T_vec, pi_tilde, l_poly, r_poly, theta_vec, y_pow_n_p, y_inv_pow_n_p, z_pow_Q_plus_1_p) =
        part1::prover_part2(
            &mut rng,
            &kzg,
            &vectors,
            W_L.clone(),
            W_R.clone(),
            W_O.clone(),
            W_U.clone(),
            c.clone(),
            I.clone(),
            &mapping,
            a_L.clone(),
            a_R.clone(),
            a_O.clone(),
            u.clone(),
            A_I,
            A_O,
            K,
            K_L,
            K_R,
            y,
            z,
            r1,
            r2,
            r3,
            l,
            m_per_vector.clone(),
            r_q.clone(),
            pi_qi.clone(),
        );

    let (x, delta, y_pow_n_v, y_inv_pow_n_v, z_pow_Q_plus_1_v) = part1::verifier_part2(
        &mut rng,
        &kzg,
        W_L.clone(),
        W_R.clone(),
        W_O.clone(),
        W_U.clone(),
        c.clone(),
        I.clone(),
        &mapping,
        A_I,
        A_O,
        K,
        y,
        z,
        T_vec.clone(),
        pi_tilde,
        n,
    );

    let (theta_vec_x, mu, l_vec, r_vec, t_tilde) = part2::prover_part1(
        &mut rng,
        &kzg,
        W_L.clone(),
        W_R.clone(),
        W_O.clone(),
        W_U.clone(),
        c.clone(),
        I.clone(),
        &mapping,
        a_L.clone(),
        a_R.clone(),
        a_O.clone(),
        u.clone(),
        A_I,
        A_O,
        K,
        y,
        z,
        r1,
        r2,
        r3,
        x,
        T_vec.clone(),
        pi_tilde,
        l_poly.clone(),
        r_poly.clone(),
        theta_vec.clone(),
    );

    let x_t = part2::verifier_part1(
        &mut rng,
        &kzg,
        W_L.clone(),
        W_R.clone(),
        W_O.clone(),
        W_U.clone(),
        c.clone(),
        I.clone(),
        &mapping,
        A_I,
        A_O,
        K,
        y,
        z,
        T_vec.clone(),
        pi_tilde,
        n,
        x,
        theta_vec_x,
        mu,
        t_tilde,
    );

    let (ipa_proof, mut transcript, commit_Wp, original_commit_Wp, val_Wp, proof_Wp) =
        part2::prover_part2(
            &mut rng,
            &kzg,
            W_L.clone(),
            W_R.clone(),
            W_O.clone(),
            W_U.clone(),
            c.clone(),
            I.clone(),
            &mapping,
            a_L.clone(),
            a_R.clone(),
            a_O.clone(),
            u.clone(),
            A_I,
            A_O,
            K,
            y,
            z,
            r1,
            r2,
            r3,
            x,
            T_vec.clone(),
            pi_tilde,
            l_poly.clone(),
            r_poly.clone(),
            theta_vec,
            theta_vec_x,
            mu,
            t_tilde,
            x_t,
            beta,
            z_pow_Q_plus_1_p,
            y_pow_n_p,
            y_inv_pow_n_p,
            l_vec,
            r_vec,
        );

    let verification_result = part2::verifier_part2(
        test_index,
        &mut rng,
        &kzg,
        V_q_affine.as_slice(),
        W_L.clone(),
        W_R.clone(),
        W_O.clone(),
        W_U.clone(),
        c.clone(),
        I.clone(),
        &mapping,
        A_I,
        A_O,
        K,
        y,
        z,
        T_vec.clone(),
        pi_tilde,
        n,
        delta,
        z_pow_Q_plus_1_v,
        x,
        theta_vec_x,
        mu,
        t_tilde,
        x_t,
        ipa_proof,
        y_pow_n_v,
        y_inv_pow_n_v,
        l,
        m_per_vector.clone(),
        beta,
        commit_Wp,
        original_commit_Wp,
        val_Wp,
        proof_Wp,
    );

    let actual_time = test_start_time.elapsed();

    println!("\n=== Test {} Runtime Statistics ===", test_index);
    println!("Runtime: {:.3} ms", actual_time.as_millis() as f64);

    Ok(actual_time)
}

/// Parameterized test function for user-specified parameter combinations
fn run_parameterized_tests() {
    println!("\n=== Parameterized Tests ===");
    println!("Testing different parameter combinations:");
    println!("1. n: 2^12, 2^13, 2^14, 2^15, 2^16");
    println!("2. m (total selected elements): 2^8, 2^9, 2^10, 2^11, 2^12, 2^13, 2^14");
    println!("3. l (vector count): 2, 3, 4, 5, 6, 7, 8, 9, 10");
    println!("4. subset: 64, 128, 256, 512, 1024");
    println!("1. n power 12");
    println!("2. n power 13");
    println!("3. n power 14");
    println!("4. n power 15");
    println!("5. n power 16");
    println!("Select test mode (1, 2, 3, 4, 5):");

    let mut input = String::new();
    std::io::stdin().read_line(&mut input).expect("Failed to read input");

    let n_values = {
        match input.trim() {
            "1" => {
                vec![4096]
            }
            "2" => {
                vec![8192]
            }
            "3" => {
                vec![16384]
            }
            "4" => {
                vec![32768]
            }
            "5" => {
                vec![65536]
            }
            _ => {
                vec![4096, 8192, 16384, 32768, 65536]
            }
        }
    };
    
    let m_values = {
        vec![256, 512, 1024, 2048, 4096, 8192, 16384] // 2^8, 2^9, 2^10, 2^11, 2^12, 2^13, 2^14
    };
    
    let l_values = {
        vec![2, 3, 4, 5, 6, 7, 8, 9, 10]
    };
     
    let subset_ratios = {
        vec![100, 200, 300, 400, 500, 600, 700, 800, 900, 1000]
    };
    
    let test_results: Vec<Result<Duration, String>> = n_values
        .iter()
        .flat_map(|&n| {
            // Create independent KZG instance for each n
            let mut rng = thread_rng();
            let degree = n * 8;
            println!("Generating Structured Reference String (SRS) for n={}...", n);
            let kzg = kzg::KZG::new(degree, &mut rng);
            println!("n={}, degree={}", n, degree);

            // Generate all valid test configurations for this n
            let configs: Vec<_> = m_values
                .iter()
                .filter(|&&total_m| total_m <= n)
                .flat_map(|&total_m| {
                    let subset_ratios_clone = subset_ratios.clone();
                    l_values.iter()
                    .flat_map(move |&l| {
                        let subset_ratios_clone2 = subset_ratios_clone.clone();
                        subset_ratios_clone2
                            .iter()
                            .filter(move |&&subset_ratio| subset_ratio <= total_m)
                            .map(move |&subset_ratio| (n, total_m, l, subset_ratio))
                            .collect::<Vec<_>>()
                    })
                })
                .collect();

            println!("n={} has {} valid test configurations", n, configs.len());

            configs
                .into_iter()
                .enumerate()
                .map(move |(local_index, (n, total_m, l, subset_ratio))| {
                    let m_per_vector_value = subset_ratio;
                    let vector_len = total_m;
                    let m_per_vector = vec![m_per_vector_value; l];
                    println!(
                        "\n--- Test (n={}, total_m={}, l={}, subset_ratio={}) ---",
                        n, total_m, l, subset_ratio
                    );
                    run_test_with_parameters(
                        local_index + 1,
                        n,
                        m_per_vector,
                        l,
                        subset_ratio,
                        vector_len,
                        &kzg,
                    )
                })
                .collect::<Vec<_>>()
        })
        .collect();

    // Statistics
    let mut total_duration = Duration::from_secs(0);
    let mut total_tests = 0;

    for (i, result) in test_results.into_iter().enumerate() {
        match result {
            Ok(duration) => {
                total_duration += duration;
                total_tests += 1;
            }
            Err(e) => {
                total_tests += 1;
            }
        }
        // Progress display
        if (i + 1) % 10 == 0 {
            println!("\n=== Progress: Completed {}/{} tests ===", i + 1, total_tests);
        }
    }

    println!("\n=== Parameterized Tests Completed ===");
    println!("=== Test Statistics ===");
    println!("• Total test combinations: {}", total_tests);
    println!("• Total test time: {:.3} ms", total_duration.as_millis() as f64);
    println!(
        "• Average test time: {:.3} ms",
        if total_tests > 0 {
            total_duration.as_millis() as f64 / total_tests as f64
        } else {
            0.0
        }
    );
}

fn run_test_with_parameters_extended(
    test_index: usize,
    n: usize, 
    m_per_vector: Vec<usize>, 
    l: usize,
    subset_ratio: usize,
    vector_len: usize,
    kzg: &KZG, 
    vectors: &Vec<Vec<Fr>>,
    r_q: &Vec<Fr>,
    V_q_affine: &Vec<G1Affine>,
    mapping: &MultiVectorMapping,
    I: Vec<usize>,
    u: Vec<Fr>,
    a_L: &Vec<Fr>,
    a_R: &Vec<Fr>,
    a_O: &Vec<Fr>,
    W_L: &Vec<Fr>,
    W_R: &Vec<Fr>,
    W_O: &Vec<Fr>,
    W_U: &Vec<Fr>,
    c: &Vec<Fr>,
    pi_qi: &Vec<G1>,
) -> Result<Duration, String> {
    let test_start_time = std::time::Instant::now();
    let mut rng = thread_rng();
    // Protocol execution
    let beta = part1::verifier_sample_beta(&mut rng);

    let (A_I, A_O, K, K_L, K_R, n, r1, r2, r3) = part1::prover_part1(
        &mut rng,
        &kzg,
        W_L.clone(),
        W_R.clone(),
        W_O.clone(),
        W_U.clone(),
        c.clone(),
        I.clone(),
        &mapping,
        a_L.clone(),
        a_R.clone(),
        a_O.clone(),
        u.clone(),
    );

    let (y, z) = part1::verifier_part1(
        &mut rng,
        &kzg,
        W_L.clone(),
        W_R.clone(),
        W_O.clone(),
        W_U.clone(),
        c.clone(),
        I.clone(),
        &mapping,
        A_I,
        A_O,
        K,
    );

    let (T_vec, pi_tilde, l_poly, r_poly, theta_vec, y_pow_n_p, y_inv_pow_n_p, z_pow_Q_plus_1_p) =
        part1::prover_part2(
            &mut rng,
            &kzg,
            &vectors,
            W_L.clone(),
            W_R.clone(),
            W_O.clone(),
            W_U.clone(),
            c.clone(),
            I.clone(),
            &mapping,
            a_L.clone(),
            a_R.clone(),
            a_O.clone(),
            u.clone(),
            A_I,
            A_O,
            K,
            K_L,
            K_R,
            y,
            z,
            r1,
            r2,
            r3,
            l,
            m_per_vector.clone(),
            r_q.clone(),
            pi_qi.clone(),
        );

    let (x, delta, y_pow_n_v, y_inv_pow_n_v, z_pow_Q_plus_1_v) = part1::verifier_part2(
        &mut rng,
        &kzg,
        W_L.clone(),
        W_R.clone(),
        W_O.clone(),
        W_U.clone(),
        c.clone(),
        I.clone(),
        &mapping,
        A_I,
        A_O,
        K,
        y,
        z,
        T_vec.clone(),
        pi_tilde,
        n,
    );

    let (theta_vec_x, mu, l_vec, r_vec, t_tilde) = part2::prover_part1(
        &mut rng,
        &kzg,
        W_L.clone(),
        W_R.clone(),
        W_O.clone(),
        W_U.clone(),
        c.clone(),
        I.clone(),
        &mapping,
        a_L.clone(),
        a_R.clone(),
        a_O.clone(),
        u.clone(),
        A_I,
        A_O,
        K,
        y,
        z,
        r1,
        r2,
        r3,
        x,
        T_vec.clone(),
        pi_tilde,
        l_poly.clone(),
        r_poly.clone(),
        theta_vec.clone(),
    );

    let x_t = part2::verifier_part1(
        &mut rng,
        &kzg,
        W_L.clone(),
        W_R.clone(),
        W_O.clone(),
        W_U.clone(),
        c.clone(),
        I.clone(),
        &mapping,
        A_I,
        A_O,
        K,
        y,
        z,
        T_vec.clone(),
        pi_tilde,
        n,
        x,
        theta_vec_x,
        mu,
        t_tilde,
    );

    let (ipa_proof, mut transcript, commit_Wp, original_commit_Wp, val_Wp, proof_Wp) =
        part2::prover_part2(
            &mut rng,
            &kzg,
            W_L.clone(),
            W_R.clone(),
            W_O.clone(),
            W_U.clone(),
            c.clone(),
            I.clone(),
            &mapping,
            a_L.clone(),
            a_R.clone(),
            a_O.clone(),
            u.clone(),
            A_I,
            A_O,
            K,
            y,
            z,
            r1,
            r2,
            r3,
            x,
            T_vec.clone(),
            pi_tilde,
            l_poly.clone(),
            r_poly.clone(),
            theta_vec,
            theta_vec_x,
            mu,
            t_tilde,
            x_t,
            beta,
            z_pow_Q_plus_1_p,
            y_pow_n_p,
            y_inv_pow_n_p,
            l_vec,
            r_vec,
        );

    let verification_result = part2::verifier_part2(
        test_index,
        &mut rng,
        &kzg,
        V_q_affine.as_slice(),
        W_L.clone(),
        W_R.clone(),
        W_O.clone(),
        W_U.clone(),
        c.clone(),
        I.clone(),
        &mapping,
        A_I,
        A_O,
        K,
        y,
        z,
        T_vec.clone(),
        pi_tilde,
        n,
        delta,
        z_pow_Q_plus_1_v,
        x,
        theta_vec_x,
        mu,
        t_tilde,
        x_t,
        ipa_proof,
        y_pow_n_v,
        y_inv_pow_n_v,
        l,
        m_per_vector.clone(),
        beta,
        commit_Wp,
        original_commit_Wp,
        val_Wp,
        proof_Wp,
    );

    let actual_time = test_start_time.elapsed();

    println!("\n=== Test {} Runtime Statistics ===", test_index);
    println!("Runtime: {:.3} ms", actual_time.as_millis() as f64);

    Ok(actual_time)
}

fn run_parameterized_test_proof() {
    let n_values = {
        vec![16384; 500]
    };
    let m_values = {
        vec![1024]
    };
    
    let l_values = {
        vec![16]
    };
     
    let subset_ratios = {
        vec![512]
    };

    // Create shared KZG instance
    let mut rng = thread_rng();
    let n_value = n_values[0];
    let degree = n_value * 8;
    println!("Generating SRS for n={}...", n_value);
    let kzg = kzg::KZG::new(degree, &mut rng);
    println!("n={}, degree={}", n_value, degree);
    let kzg_arc = Arc::new(kzg.clone());

    let l = l_values[0];
    let m_per_vector_value = subset_ratios[0];
    let vector_len = m_values[0];
    let m_per_vector = vec![m_per_vector_value; l];

    let total_m: usize = m_per_vector.iter().sum(); // Total selected elements
    let degree = n_value * 8; // Max polynomial degree

    // Step 1: Generate test vectors
    let vectors: Vec<Vec<Fr>> = (0..l)
        .into_par_iter()
        .map(|q| {
            (0..vector_len)
                .map(|j| Fr::from((q as u64 + 1) * 1000 + j as u64))
                .collect()
        })
        .collect();

    // Step 2: Generate random blinding factors for each vector
    let r_q: Vec<Fr> = (0..l)
        .into_par_iter()
        .map_init(|| thread_rng(), |rng, _| Fr::rand(rng))
        .collect();

    // Step 3: Create commitments V_q for each vector
    let V_q: Vec<G1> = (0..l)
        .into_par_iter()
        // .into_iter()
        .map(|q| {
            let mut V = G1::zero();
            let N = n_value;
            V += kzg.srs.g1[N] * r_q[q];
            for j in 0..vectors[q].len() {
                V += kzg.srs.g1[j + 1] * vectors[q][j];
            }
            V
        })
        .collect();

    // Convert V_q to affine for verification
    let V_q_affine: Vec<_> = V_q.iter().map(|v| v.into_affine()).collect();

    // Step 4: Select elements and build M mapping
    let (mappings, selected_values): (Vec<Vec<usize>>, Vec<Fr>) = (0..l)
        .into_par_iter()
        .map(|q| {
            let mut available_indices: Vec<usize> = (0..vectors[q].len()).collect();
            available_indices.shuffle(&mut thread_rng());

            let mut M_q = Vec::new();
            let mut values = Vec::new();
            let max_count = m_per_vector[q].min(available_indices.len());

            for i in 0..max_count {
                let idx = available_indices[i];
                M_q.push(idx);
                values.push(vectors[q][idx]);
            }

            (M_q, values)
        })
        .fold(
            || (Vec::new(), Vec::new()),
            |(mut maps, mut vals), (map, val)| {
                maps.push(map);
                vals.extend(val);
                (maps, vals)
            }
        )
        .reduce(
            || (Vec::new(), Vec::new()),
            |(mut maps1, mut vals1), (maps2, vals2)| {
                maps1.extend(maps2);
                vals1.extend(vals2);
                (maps1, vals1)
            }
        );

    let mapping = MultiVectorMapping {
        mappings: mappings.clone(),
        vector_lengths: vectors.iter().map(|v| v.len()).collect(),
    };

    // Step 5: Build flattened index set I
    let I: Vec<usize> = (0..total_m).collect();
    // Step 6: Build flattened u vector (all selected values)
    let u: Vec<Fr> = selected_values;
    // Step 7: Convert 2D M mapping to 1D
    let M_flat: Vec<usize> = mappings.iter().flatten().cloned().collect();

    // Step 8: Create circuit witness (Hadamard product constraint: a_L ◦ a_R = a_O)
    let results: Vec<(Fr, Fr, Fr)> = (0..n_value)
        .into_par_iter()
        .map(|_| {
            let a_l = Fr::rand(&mut thread_rng());
            let a_r = Fr::rand(&mut thread_rng());
            let a_o = a_l * a_r;
            (a_l, a_r, a_o)
        })
        .collect();
    let (a_L, a_R, a_O): (Vec<Fr>, Vec<Fr>, Vec<Fr>) = results.into_iter().fold(
        (Vec::new(), Vec::new(), Vec::new()),
        |(mut a_l_vec, mut a_r_vec, mut a_o_vec), (a_l, a_r, a_o)| {
            a_l_vec.push(a_l);
            a_r_vec.push(a_r);
            a_o_vec.push(a_o);
            (a_l_vec, a_r_vec, a_o_vec)
        }
    );

    // Step 9: Create circuit constraint parameters
    let results: Vec<(Fr, Fr, Fr, Fr)> = (0..n_value)
        .into_par_iter()
        .map(|_| {
            let w_l = Fr::rand(&mut thread_rng());
            let w_r = Fr::rand(&mut thread_rng());
            let w_o = Fr::rand(&mut thread_rng());
            let w_u = Fr::rand(&mut thread_rng());
            (w_l, w_r, w_o, w_u)
        })
        .collect();
    let (W_L, W_R, W_O, W_U): (Vec<Fr>, Vec<Fr>, Vec<Fr>, Vec<Fr>) = results.into_iter().fold(
        (Vec::new(), Vec::new(), Vec::new(), Vec::new()),
        |(mut w_l_vec, mut w_r_vec, mut w_o_vec, mut w_u_vec), (w_l, w_r, w_o, w_u)| {
            w_l_vec.push(w_l);
            w_r_vec.push(w_r);
            w_o_vec.push(w_o);
            w_u_vec.push(w_u);
            (w_l_vec, w_r_vec, w_o_vec, w_u_vec)
        }
    );

    let c: Vec<Fr> = (0..n_value)
        .into_par_iter()
        .map(|i| {
            let left = W_L[i] * a_L[i] + W_R[i] * a_R[i] + W_O[i] * a_O[i];
            let w_u_u = if i < total_m { W_U[i] * u[i] } else { Fr::zero() };
            left - w_u_u
        })
        .collect();

    let mut pi_qi = Vec::new();
    for q in 0..l {
        let m_q = mapping.m_q(q);
        // Inner aggregation: Σ_{i=1}^{m_q} z^i · [π_{q,i}]_1
        for i in 0..m_q {
            let mapped_idx = mapping.get(q, i); // M(q,i)
            
            // Generate [π_{q,i}]_1 = [r_q · β^{2N+1-M(q,i)}]_1 
            //                   + Σ_{j≠M(q,i)} [v_{q,j} · β^{N+1-M(q,i)+j}]_1
            let mut pi_qiq = G1::zero();
            
            // Part 1: r_q · β^{2N+1-M(q,i)}
            if mapped_idx > 2 * n_value + 1 {
                panic!("Index overflow: mapped_idx={} > 2*N+1={}", mapped_idx, 2 * n_value + 1);
            }
            let exp1 = 2 * n_value + 1 - mapped_idx;
            pi_qiq += kzg.srs.g1[exp1] * r_q[q];
            
            // Part 2: Σ_{j≠M(q,i)} [v_{q,j} · β^{N+1-M(q,i)+j}]_1
            // Note: iterate over all elements of the original vector, not just the selected one
            for (j, &v_qj) in vectors[q].iter().enumerate() {
                if j != mapped_idx {
                    // Safety check: ensure index calculation does not overflow
                    if mapped_idx > n_value + 1 + j {
                        panic!("Index overflow: mapped_idx={} > N+1+j={}", mapped_idx, n_value + 1 + j);
                    }
                    let exp2 = n_value + 1 - mapped_idx + j;
                    pi_qiq += kzg.srs.g1[exp2] * v_qj;
                }
            }
            pi_qi.push(pi_qiq);
        }
    }

    let configs: Vec<_> = m_values
        .par_iter()
        .filter(|&&total_m| total_m <= n_value)
        .flat_map(|&total_m| {
            let subset_ratios_clone = subset_ratios.clone();
            l_values.par_iter().flat_map(move |&l| {
                let subset_ratios_clone2 = subset_ratios_clone.clone();
                subset_ratios_clone2
                    .par_iter()
                    .filter(move |&&subset_ratio| subset_ratio <= total_m)
                    .map(move |&subset_ratio| (n_value, total_m, l, subset_ratio))
                    .collect::<Vec<_>>()
            })
        })
        .collect();
    println!("n={} has {} valid test configurations", n_value, configs.len());

    let start_time = std::time::Instant::now();
    let test_results: Vec<Result<Duration, String>> = n_values.into_par_iter()
        .flat_map(|n| {  
            let kzg_clone = Arc::clone(&kzg_arc);
            configs.par_iter()
                .enumerate()
                .map({
                    let m_per_vector_clone = m_per_vector.clone();
                    let vectors_clone = vectors.clone();
                    let r_q_clone = r_q.clone();
                    let V_q_affine_clone = V_q_affine.clone();
                    let mapping_clone = mapping.clone();
                    let a_L_clone = a_L.clone();
                    let a_R_clone = a_R.clone();
                    let a_O_clone = a_O.clone();
                    let W_L_clone = W_L.clone();
                    let W_R_clone = W_R.clone();
                    let W_O_clone = W_O.clone();
                    let W_U_clone = W_U.clone();
                    let c_clone = c.clone();
                    let I_clone = I.clone();
                    let u_clone = u.clone();
                    let pi_qi_clone = pi_qi.clone();
                    
                    move |(local_index, (n, total_m, l, subset_ratio))|{
                        let kzg_ref = Arc::clone(&kzg_clone);
                        run_test_with_parameters_extended(
                            local_index + 1, 
                            *n, 
                            m_per_vector_clone.clone(), 
                            *l, 
                            *subset_ratio, 
                            vector_len, 
                            &*kzg_ref, 
                            &vectors_clone, 
                            &r_q_clone, 
                            &V_q_affine_clone, 
                            &mapping_clone, 
                            I_clone.clone(), 
                            u_clone.clone(), 
                            &a_L_clone, &a_R_clone, &a_O_clone, 
                            &W_L_clone, &W_R_clone, &W_O_clone, &W_U_clone, 
                            &c_clone,
                            &pi_qi_clone
                        )
                    }
                })
                .collect::<Vec<_>>()
        })
        .collect();

    let actual_time = start_time.elapsed();

    // Statistics
    let mut successful_tests = 0;
    let mut failed_tests = 0;
    for (i, result) in test_results.into_iter().enumerate() {
        match result {
            Ok(duration) => {
                println!(
                    "✅ Test #{} completed",
                    i + 1,
                );
                successful_tests += 1;
            }
            Err(e) => {
                println!("❌ Test #{} failed: {}", i + 1, e);
                failed_tests += 1;
            }
        }
        if (i + 1) % 10 == 0 {
            println!(
                "\n=== Progress: Completed {}/{} tests ===",
                i + 1,
                successful_tests + failed_tests
            );
        }
    }

    let total_tests = successful_tests + failed_tests;
    println!("\n=== All Tests Runtime Statistics ===");
    println!("Total test runtime: {:.3} ms", actual_time.as_millis() as f64);
    println!(
        "• Average test time: {:.3} ms",
        if total_tests > 0 {
            actual_time.as_millis() as f64 / total_tests as f64
        } else {
            0.0
        }
    );
}

fn run_parameterized_test_verify() {
    println!("=== Verification Time Test (verifier_part2_stage2) ===");
    println!("This test measures verification performance specifically\n");

    let n_values = {
        vec![16384; 500]
    };
    let m_values = {
        vec![1024]
    };
    
    let l_values = {
        vec![16]
    };
     
    let subset_ratios = {
        vec![512]
    };

    // Create shared KZG instance
    let mut rng = thread_rng();
    let n_value = n_values[0];
    let degree = n_value * 8;
    println!("Generating SRS for n={}...", n_value);
    let kzg = kzg::KZG::new(degree, &mut rng);
    println!("n={}, degree={}", n_value, degree);

    let m_per_vector_value = subset_ratios[0];
    let vector_len = m_values[0];
    let l = l_values[0];
    let n = n_values[0];
    let m_per_vector = vec![m_per_vector_value; l];
    let total_m: usize = m_per_vector.iter().sum();

    println!(
        "\n--- Test (n={}, total_m={}, l={}, subset_ratio={}) ---",
        n_values[0], m_values[0], l_values[0], subset_ratios[0]
    );

    // Generate test vectors
    let vectors: Vec<Vec<Fr>> = (0..l)
        .into_par_iter()
        .map(|q| {
            (0..vector_len)
                .map(|j| Fr::from((q as u64 + 1) * 1000 + j as u64))
                .collect()
        })
        .collect();

    // Generate blinding factors
    let r_q: Vec<Fr> = (0..l)
        .into_par_iter()
        .map_init(|| thread_rng(), |rng, _| Fr::rand(rng))
        .collect();

    // Create commitments
    let V_q: Vec<G1> = (0..l)
        .into_par_iter()
        .map(|q| {
            let mut V = G1::zero();
            let N = n;
            V += kzg.srs.g1[N] * r_q[q];
            for j in 0..vectors[q].len() {
                V += kzg.srs.g1[j + 1] * vectors[q][j];
            }
            V
        })
        .collect();
    let V_q_affine: Vec<_> = V_q.iter().map(|v| v.into_affine()).collect();

    // Select elements and build mapping
    let (mappings, selected_values): (Vec<Vec<usize>>, Vec<Fr>) = (0..l)
        .into_par_iter()
        .map(|q| {
            let mut available_indices: Vec<usize> = (0..vectors[q].len()).collect();
            available_indices.shuffle(&mut thread_rng());

            let mut M_q = Vec::new();
            let mut values = Vec::new();
            let max_count = m_per_vector[q].min(available_indices.len());

            for i in 0..max_count {
                let idx = available_indices[i];
                M_q.push(idx);
                values.push(vectors[q][idx]);
            }

            (M_q, values)
        })
        .fold(
            || (Vec::new(), Vec::new()),
            |(mut maps, mut vals), (map, val)| {
                maps.push(map);
                vals.extend(val);
                (maps, vals)
            }
        )
        .reduce(
            || (Vec::new(), Vec::new()),
            |(mut maps1, mut vals1), (maps2, vals2)| {
                maps1.extend(maps2);
                vals1.extend(vals2);
                (maps1, vals1)
            }
        );

    let mapping = MultiVectorMapping {
        mappings: mappings.clone(),
        vector_lengths: vectors.iter().map(|v| v.len()).collect(),
    };

    let I: Vec<usize> = (0..total_m).collect();
    let u: Vec<Fr> = selected_values;
    let M_flat: Vec<usize> = mappings.iter().flatten().cloned().collect();

    // Create circuit witness
    let results: Vec<(Fr, Fr, Fr)> = (0..n)
        .into_par_iter()
        .map(|_| {
            let a_l = Fr::rand(&mut thread_rng());
            let a_r = Fr::rand(&mut thread_rng());
            let a_o = a_l * a_r;
            (a_l, a_r, a_o)
        })
        .collect();
    let (a_L, a_R, a_O): (Vec<Fr>, Vec<Fr>, Vec<Fr>) = results.into_iter().fold(
        (Vec::new(), Vec::new(), Vec::new()),
        |(mut a_l_vec, mut a_r_vec, mut a_o_vec), (a_l, a_r, a_o)| {
            a_l_vec.push(a_l);
            a_r_vec.push(a_r);
            a_o_vec.push(a_o);
            (a_l_vec, a_r_vec, a_o_vec)
        }
    );

    // Create circuit constraints
    let results: Vec<(Fr, Fr, Fr, Fr)> = (0..n)
        .into_par_iter()
        .map(|_| {
            let w_l = Fr::rand(&mut thread_rng());
            let w_r = Fr::rand(&mut thread_rng());
            let w_o = Fr::rand(&mut thread_rng());
            let w_u = Fr::rand(&mut thread_rng());
            (w_l, w_r, w_o, w_u)
        })
        .collect();
    let (W_L, W_R, W_O, W_U): (Vec<Fr>, Vec<Fr>, Vec<Fr>, Vec<Fr>) = results.into_iter().fold(
        (Vec::new(), Vec::new(), Vec::new(), Vec::new()),
        |(mut w_l_vec, mut w_r_vec, mut w_o_vec, mut w_u_vec), (w_l, w_r, w_o, w_u)| {
            w_l_vec.push(w_l);
            w_r_vec.push(w_r);
            w_o_vec.push(w_o);
            w_u_vec.push(w_u);
            (w_l_vec, w_r_vec, w_o_vec, w_u_vec)
        }
    );

    let c: Vec<Fr> = (0..n)
        .into_par_iter()
        .map(|i| {
            let left = W_L[i] * a_L[i] + W_R[i] * a_R[i] + W_O[i] * a_O[i];
            let w_u_u = if i < total_m { W_U[i] * u[i] } else { Fr::zero() };
            left - w_u_u
        })
        .collect();

    let mut pi_qi = Vec::new();
    for q in 0..l {
        let m_q = mapping.m_q(q);
        // Inner aggregation: Σ_{i=1}^{m_q} z^i · [π_{q,i}]_1
        for i in 0..m_q {
            let mapped_idx = mapping.get(q, i); // M(q,i)
            
            // Generate [π_{q,i}]_1 = [r_q · β^{2N+1-M(q,i)}]_1 
            //                   + Σ_{j≠M(q,i)} [v_{q,j} · β^{N+1-M(q,i)+j}]_1
            let mut pi_qiq = G1::zero();
            
            // Part 1: r_q · β^{2N+1-M(q,i)}
            if mapped_idx > 2 * n + 1 {
                panic!("Index overflow: mapped_idx={} > 2*N+1={}", mapped_idx, 2 * n + 1);
            }
            let exp1 = 2 * n + 1 - mapped_idx;
            pi_qiq += kzg.srs.g1[exp1] * r_q[q];
            
            // Part 2: Σ_{j≠M(q,i)} [v_{q,j} · β^{N+1-M(q,i)+j}]_1
            // Note: iterate over all elements of the original vector, not just the selected one
            for (j, &v_qj) in vectors[q].iter().enumerate() {
                if j != mapped_idx {
                    // Safety check: ensure index calculation does not overflow
                    if mapped_idx > n + 1 + j {
                        panic!("Index overflow: mapped_idx={} > N+1+j={}", mapped_idx, n + 1 + j);
                    }
                    let exp2 = n + 1 - mapped_idx + j;
                    pi_qiq += kzg.srs.g1[exp2] * v_qj;
                }
            }
            pi_qi.push(pi_qiq);
        }
    }

    // Protocol execution
    let beta = part1::verifier_sample_beta(&mut rng);

    let (A_I, A_O, K, K_L, K_R, n, r1, r2, r3) = part1::prover_part1(
        &mut rng,
        &kzg,
        W_L.clone(),
        W_R.clone(),
        W_O.clone(),
        W_U.clone(),
        c.clone(),
        I.clone(),
        &mapping,
        a_L.clone(),
        a_R.clone(),
        a_O.clone(),
        u.clone(),
    );

    let (y, z) = part1::verifier_part1(
        &mut rng,
        &kzg,
        W_L.clone(),
        W_R.clone(),
        W_O.clone(),
        W_U.clone(),
        c.clone(),
        I.clone(),
        &mapping,
        A_I,
        A_O,
        K,
    );

    let (T_vec, pi_tilde, l_poly, r_poly, theta_vec, y_pow_n_p, y_inv_pow_n_p, z_pow_Q_plus_1_p) =
        part1::prover_part2(
            &mut rng,
            &kzg,
            &vectors,
            W_L.clone(),
            W_R.clone(),
            W_O.clone(),
            W_U.clone(),
            c.clone(),
            I.clone(),
            &mapping,
            a_L.clone(),
            a_R.clone(),
            a_O.clone(),
            u.clone(),
            A_I,
            A_O,
            K,
            K_L,
            K_R,
            y,
            z,
            r1,
            r2,
            r3,
            l,
            m_per_vector.clone(),
            r_q.clone(),
            pi_qi.clone(),
        );

    let (x, delta, y_pow_n_v, y_inv_pow_n_v, z_pow_Q_plus_1_v) = part1::verifier_part2(
        &mut rng,
        &kzg,
        W_L.clone(),
        W_R.clone(),
        W_O.clone(),
        W_U.clone(),
        c.clone(),
        I.clone(),
        &mapping,
        A_I,
        A_O,
        K,
        y,
        z,
        T_vec.clone(),
        pi_tilde,
        n,
    );

    let (theta_vec_x, mu, l_vec, r_vec, t_tilde) = part2::prover_part1(
        &mut rng,
        &kzg,
        W_L.clone(),
        W_R.clone(),
        W_O.clone(),
        W_U.clone(),
        c.clone(),
        I.clone(),
        &mapping,
        a_L.clone(),
        a_R.clone(),
        a_O.clone(),
        u.clone(),
        A_I,
        A_O,
        K,
        y,
        z,
        r1,
        r2,
        r3,
        x,
        T_vec.clone(),
        pi_tilde,
        l_poly.clone(),
        r_poly.clone(),
        theta_vec.clone(),
    );

    let x_t = part2::verifier_part1(
        &mut rng,
        &kzg,
        W_L.clone(),
        W_R.clone(),
        W_O.clone(),
        W_U.clone(),
        c.clone(),
        I.clone(),
        &mapping,
        A_I,
        A_O,
        K,
        y,
        z,
        T_vec.clone(),
        pi_tilde,
        n,
        x,
        theta_vec_x,
        mu,
        t_tilde,
    );

    let (ipa_proof, mut transcript, commit_Wp, original_commit_Wp, val_Wp, proof_Wp) =
        part2::prover_part2(
            &mut rng,
            &kzg,
            W_L.clone(),
            W_R.clone(),
            W_O.clone(),
            W_U.clone(),
            c.clone(),
            I.clone(),
            &mapping,
            a_L.clone(),
            a_R.clone(),
            a_O.clone(),
            u.clone(),
            A_I,
            A_O,
            K,
            y,
            z,
            r1,
            r2,
            r3,
            x,
            T_vec.clone(),
            pi_tilde,
            l_poly.clone(),
            r_poly.clone(),
            theta_vec,
            theta_vec_x,
            mu,
            t_tilde,
            x_t,
            beta,
            z_pow_Q_plus_1_p,
            y_pow_n_p,
            y_inv_pow_n_p,
            l_vec,
            r_vec,
        );

    let P_prime = match part2::verifier_part2_stage1(
        &mut rng,
        &kzg,
        V_q_affine.as_slice(),
        W_L.clone(),
        W_R.clone(),
        W_O.clone(),
        W_U.clone(),
        c.clone(),
        I.clone(),
        &mapping,
        A_I,
        A_O,
        K,
        y,
        z,
        T_vec.clone(),
        pi_tilde,
        n,
        delta,
        z_pow_Q_plus_1_v.clone(),
        x,
        theta_vec_x,
        mu,
        t_tilde,
        x_t,
        ipa_proof.clone(),
        y_pow_n_v.clone(),
        y_inv_pow_n_v.clone(),
        l,
        m_per_vector.clone(),
        beta,
        commit_Wp,
        original_commit_Wp,
        val_Wp,
        proof_Wp,
    ) {
        Ok(p_prime) => p_prime,
        Err(e) => {
            println!("❌ verifier_part2_stage1 failed: {}", e);
            return;
        }
    };

    // Prepare parameters for verification benchmark
    let kzg_clone = Arc::new(kzg.clone());
    let v_q_affine_clone = V_q_affine.clone();
    let c_clone = c.clone();
    let mapping_clone = mapping.clone();
    let t_vec_clone = T_vec.clone();
    let z_pow_q_plus_1_clone = z_pow_Q_plus_1_v.clone();
    let ipa_proof_clone = ipa_proof.clone();
    let y_pow_n_clone = y_pow_n_v.clone();
    let y_inv_pow_n_clone = y_inv_pow_n_v.clone();

    // Run verification benchmark
    let num_tests = 500;
    let start = std::time::Instant::now();
    let verification_results: Vec<(bool, Duration)> = (0..num_tests)
        .into_par_iter()
        .map(|i| {
            let mut local_rng = thread_rng();
            let verify_start = std::time::Instant::now();

            let verification_result = part2::verifier_part2_stage2(
                &mut local_rng,
                i + 1,
                &kzg_clone,
                v_q_affine_clone.as_slice(),
                c_clone.clone(),
                &mapping_clone,
                z,
                t_vec_clone.clone(),
                pi_tilde,
                n,
                delta,
                z_pow_q_plus_1_clone.clone(),
                x,
                theta_vec_x,
                t_tilde,
                x_t,
                ipa_proof_clone.clone(),
                y_pow_n_clone.clone(),
                y_inv_pow_n_clone.clone(),
                l,
                P_prime,
            );

            let verify_duration = verify_start.elapsed();
            (verification_result, verify_duration)
        })
        .collect();

    let total_time = start.elapsed();
    let total_verify_time: Duration = verification_results
        .iter()
        .map(|(_, duration)| *duration)
        .sum();
    let successful_tests = verification_results
        .iter()
        .filter(|(result, _)| *result)
        .count();

    println!("\n=== Verification Time Test Results ===");
    println!("• Total verification time: {:.3} ms", total_time.as_millis() as f64);
    println!(
        "• Fastest verification: {:.3} ms",
        verification_results
            .iter()
            .map(|(_, d)| d.as_millis())
            .min()
            .unwrap_or(0) as f64
    );
    println!(
        "• Slowest verification: {:.3} ms",
        verification_results
            .iter()
            .map(|(_, d)| d.as_millis())
            .max()
            .unwrap_or(0) as f64
    );
    println!(
        "• Average verification: {:.3} ms",
        total_time.as_millis() as f64 / num_tests as f64
    );
}

/// Run group operation benchmark tests
fn run_benchmark_tests() {
    println!("=== Group Operation Benchmark ===");
    println!("Each test runs 1000 times and calculates average time\n");

    let mut rng = thread_rng();

    // Test 1: G1 addition [a]_1 + [b]_1
    benchmark_g1_addition(&mut rng);
    // Test 2: G2 addition [a]_2 + [b]_2
    benchmark_g2_addition(&mut rng);
    // Test 3: G1 scalar multiplication a * [b]_1
    benchmark_g1_scalar_multiplication(&mut rng);
    // Test 4: G2 scalar multiplication a * [b]_2
    benchmark_g2_scalar_multiplication(&mut rng);
    // Test 5: Pairing operation e([a]_1, [b]_2)
    benchmark_pairing(&mut rng);
}

/// Benchmark G1 group addition
fn benchmark_g1_addition(rng: &mut impl Rng) {
    println!("Test 1: G1 Addition [a]_1 + [b]_1");

    let mut total_duration = Duration::new(0, 0);
    const ITERATIONS: usize = 1000;

    for _ in 0..ITERATIONS {
        let a = G1::rand(rng);
        let b = G1::rand(rng);

        let start = SystemTime::now();
        let _result = a + b;
        let duration = start.elapsed().unwrap_or(Duration::new(0, 0));
        total_duration += duration;
    }

    let avg_duration = total_duration / ITERATIONS as u32;
    println!("  Average: {:.3} μs", avg_duration.as_micros() as f64);
    println!("  Total: {:.3} ms\n", total_duration.as_millis() as f64);
}

/// Benchmark G2 group addition
fn benchmark_g2_addition(rng: &mut impl Rng) {
    println!("Test 2: G2 Addition [a]_2 + [b]_2");

    use ark_bn254::G2Projective as G2;

    let mut total_duration = Duration::new(0, 0);
    const ITERATIONS: usize = 1000;

    for _ in 0..ITERATIONS {
        let a = G2::rand(rng);
        let b = G2::rand(rng);

        let start = SystemTime::now();
        let _result = a + b;
        let duration = start.elapsed().unwrap_or(Duration::new(0, 0));
        total_duration += duration;
    }

    let avg_duration = total_duration / ITERATIONS as u32;
    println!("  Average: {:.3} μs", avg_duration.as_micros() as f64);
    println!("  Total: {:.3} ms\n", total_duration.as_millis() as f64);
}

/// Benchmark G1 scalar multiplication
fn benchmark_g1_scalar_multiplication(rng: &mut impl Rng) {
    println!("Test 3: G1 Scalar Multiplication a * [b]_1");

    let mut total_duration = Duration::new(0, 0);
    const ITERATIONS: usize = 1000;

    for _ in 0..ITERATIONS {
        let scalar = Fr::rand(rng);
        let point = G1::rand(rng);

        let start = SystemTime::now();
        let _result = point * scalar;
        let duration = start.elapsed().unwrap_or(Duration::new(0, 0));
        total_duration += duration;
    }

    let avg_duration = total_duration / ITERATIONS as u32;
    println!("  Average: {:.3} μs", avg_duration.as_micros() as f64);
    println!("  Total: {:.3} ms\n", total_duration.as_millis() as f64);
}

/// Benchmark G2 scalar multiplication
fn benchmark_g2_scalar_multiplication(rng: &mut impl Rng) {
    println!("Test 4: G2 Scalar Multiplication a * [b]_2");

    use ark_bn254::G2Projective as G2;

    let mut total_duration = Duration::new(0, 0);
    const ITERATIONS: usize = 1000;

    for _ in 0..ITERATIONS {
        let scalar = Fr::rand(rng);
        let point = G2::rand(rng);

        let start = SystemTime::now();
        let _result = point * scalar;
        let duration = start.elapsed().unwrap_or(Duration::new(0, 0));
        total_duration += duration;
    }

    let avg_duration = total_duration / ITERATIONS as u32;
    println!("  Average: {:.3} μs", avg_duration.as_micros() as f64);
    println!("  Total: {:.3} ms\n", total_duration.as_millis() as f64);
}

/// Benchmark pairing operation
fn benchmark_pairing(rng: &mut impl Rng) {
    println!("Test 5: Pairing Operation e([a]_1, [b]_2)");

    use ark_bn254::{G2Projective as G2, G1Affine, G2Affine};
    use ark_ec::pairing::Pairing;

    let mut total_duration = Duration::new(0, 0);
    const ITERATIONS: usize = 1000;

    for _ in 0..ITERATIONS {
        let g1_point = G1::rand(rng).into_affine();
        let g2_point = G2::rand(rng).into_affine();

        let start = SystemTime::now();
        let _result = ark_bn254::Bn254::pairing(g1_point, g2_point);
        let duration = start.elapsed().unwrap_or(Duration::new(0, 0));
        total_duration += duration;
    }

    let avg_duration = total_duration / ITERATIONS as u32;
    println!("  Average: {:.3} μs", avg_duration.as_micros() as f64);
    println!("  Total: {:.3} ms\n", total_duration.as_millis() as f64);
}

fn run_test_commitment() {
    let mut rng = thread_rng();
    let vector_len = 10;
    let N = vector_len;
    let degree = vector_len * 2;
    println!("Generating Structured Reference String (SRS)...");
    let kzg = kzg::KZG::new(degree, &mut rng);

    // Create test vector
    let vector: Vec<Fr> = (0..vector_len).map(|j| Fr::from(j as u64 + 1)).collect();
    let r = Fr::rand(&mut rng);

    // Benchmark commitment creation (500 iterations)
    const ITERATIONS: usize = 500;
    let durations: Vec<std::time::Duration> = (0..ITERATIONS)
        .into_par_iter()
        .map(|i| {
            let v_q_start = std::time::Instant::now();
            let mut V = G1::zero();
            V += kzg.srs.g1[N] * r;

            // Parallel sum for commitment
            let partial_sums: Vec<G1> = (0..vector.len())
                .into_par_iter()
                .map(|j| kzg.srs.g1[j] * vector[j])
                .collect();

            for partial in partial_sums {
                V += partial;
            }

            let v_q_duration = v_q_start.elapsed();
            println!(
                "Run {}: Commitment created, time: {:.3} ms",
                i + 1,
                v_q_duration.as_millis() as f64
            );
            v_q_duration
        })
        .collect();

    // Statistics
    let total_duration: std::time::Duration = durations.iter().sum();
    let avg_duration = total_duration / ITERATIONS as u32;
    let default_duration = std::time::Duration::new(0, 0);
    let min_duration = durations.iter().min().unwrap_or(&default_duration);
    let max_duration = durations.iter().max().unwrap_or(&default_duration);

    println!("=== Vector Commitment Performance ===");
    println!("Iterations: {}", ITERATIONS);
    println!("Average: {:.3} ms", avg_duration.as_millis() as f64);
    println!("Minimum: {:.3} ms", min_duration.as_millis() as f64);
    println!("Maximum: {:.3} ms", max_duration.as_millis() as f64);
    println!("Total: {:.3} ms", total_duration.as_millis() as f64);
}

fn run_test_commitment_opt() {
    let mut rng = thread_rng();
    let db_size = 1000000;
    let N = db_size;
    let degree = 2 * db_size + 10;
    println!("Generating SRS... (degree={})", degree);

    let setup_time = std::time::Instant::now();
    let kzg = kzg::KZG::new(degree, &mut rng);
    println!(
        "SRS generation complete, time: {:.3} ms",
        setup_time.elapsed().as_millis() as f64
    );

    // 1. AuthDele(DB)
    let db: Vec<Fr> = (0..db_size).map(|_| Fr::rand(&mut rng)).collect();
    let r = Fr::rand(&mut rng);

    let auth_dele_start = std::time::Instant::now();
    let sigma = {
        let mut s = kzg.srs.g1[N] * r;
        s += db
            .par_iter()
            .enumerate()
            .map(|(i, x)| kzg.srs.g1[i] * x)
            .reduce(|| G1::zero(), |a, b| a + b);
        s
    };
    let auth_dele_time = auth_dele_start.elapsed();
    println!("AuthDele time: {:.3} ms", auth_dele_time.as_millis() as f64);

    // 2. AuthChal(sigma, |DB|)
    let auth_chal = |sigma: &G1, db_size: usize| -> Vec<Fr> {
        let sigma_bytes = {
            let mut v = Vec::new();
            sigma.into_affine().serialize_compressed(&mut v).unwrap();
            v
        };
        (0..db_size)
            .into_par_iter()
            .map(|i| {
                let mut hasher = Sha256::new();
                hasher.update(&sigma_bytes);
                hasher.update(&i.to_le_bytes());
                Fr::from_le_bytes_mod_order(&hasher.finalize())
            })
            .collect()
    };

    // Benchmark AuthChal
    let repeat = 500;
    let chal_start = SystemTime::now();
    let chal_results: Vec<(Vec<Fr>, Duration)> = (0..repeat)
        .into_par_iter()
        .map(|i| {
            let start = SystemTime::now();
            let challenge = auth_chal(&sigma, db_size);
            let elapsed = start.elapsed().unwrap_or(Duration::new(0, 0));
            println!(
                "AuthChal Run {}: time: {:.3} ms",
                i + 1,
                elapsed.as_millis() as f64
            );
            (challenge, elapsed)
        })
        .collect();
    let chal_elapsed = chal_start.elapsed().unwrap_or(Duration::new(0, 0));
    println!(
        "Average AuthChal time: {:.3} ms",
        chal_elapsed.as_millis() as f64 / repeat as f64
    );

    let challenge_set = auth_chal(&sigma, db_size);

    // 3. AuthResp(pp, DB, sigma, Q)
    let auth_resp_start = std::time::Instant::now();

    // Compute open proofs
    let open_proofs: Vec<G1> = (0..db_size)
        .into_par_iter()
        .map(|i| {
            let mut pi_qi = kzg.srs.g1[2 * N + 1 - i] * r;
            pi_qi += db
                .par_iter()
                .enumerate()
                .filter(|&(j, _)| j != i)
                .map(|(j, &v_qj)| kzg.srs.g1[N + 1 - i + j] * v_qj)
                .reduce(|| G1::zero(), |a, b| a + b);
            pi_qi
        })
        .collect();

    // Compute pi_dele
    let pi_dele: G1 = open_proofs
        .par_iter()
        .zip(challenge_set.par_iter())
        .map(|(p, theta)| *p * *theta)
        .reduce(|| G1::zero(), |a, b| a + b);

    let reversed_challenge_set: Vec<Fr> = challenge_set.par_iter().rev().cloned().collect();

    // Compute aux, aux1
    let aux: G2 = challenge_set
        .par_iter()
        .enumerate()
        .map(|(i, theta)| kzg.srs.g2[N + 1 - i] * *theta)
        .reduce(|| G2::zero(), |a, b| a + b);

    let aux1: G1 = challenge_set
        .par_iter()
        .enumerate()
        .map(|(i, theta)| kzg.srs.g1[N + 1 - i] * *theta)
        .reduce(|| G1::zero(), |a, b| a + b);

    let (value_aux, proof_aux) = kzg.open_shifted_at(&reversed_challenge_set, 2, r, N);
    let auth_resp_time = auth_resp_start.elapsed();
    println!("AuthResp time: {:.3} ms", auth_resp_time.as_millis() as f64);

     // 4. AuthVry(pp, sigma, Q, R, DB)
    let auth_vry = |db_size: usize,
                    sigma: &G1,
                    db: &[Fr],
                    challenge_set: &[Fr],
                    open_proofs: &[G1],
                    aggregated: &G1,
                    aux: &G2,
                    aux1: &G1,
                    proof_aux: &G1,
                    value_aux: Fr,
                    r: &Fr|
     -> bool {
        // Parallel verification of three conditions
        let (verification1, (verification2, verification3)) = rayon::join(
            || {
                // Verify aux correctness
                let (beta_pow_deg_diff, beta_minus_point_g2) = rayon::join(
                    || {
                        let degree_diff = db_size;
                        kzg.srs.g2[degree_diff]
                    },
                    || {
                        kzg.srs.g2[0].mul(r.neg()).add(&kzg.srs.g2[1])
                    }
                );
                if beta_pow_deg_diff == G2::zero() { return false; }

                let (left_pairing, right_pairing) = rayon::join(
                    || Bn254::pairing( (G1::from(*aux1) - kzg.srs.g1[0].mul(value_aux)).into_affine(), beta_pow_deg_diff ),
                    || Bn254::pairing(proof_aux.into_affine(), beta_minus_point_g2.into_affine())
                );
                left_pairing == right_pairing
            },
            || rayon::join(
                || {
                    // Verify aux consistency
                    let (left, right) = rayon::join(
                        || Bn254::pairing( aux1.into_affine(), kzg.srs.g2[0].into_affine() ),
                        || Bn254::pairing(kzg.srs.g1[0].into_affine(), aux.into_affine())
                    );
                    left == right
                },
                || {
                    // Verify pairing equation
                    // μ = Σ(θ_i × x_i)
                    let mu: Fr = challenge_set
                        .par_iter()
                        .zip(db.par_iter())
                        .map(|(theta, x)| *theta * *x)
                        .reduce(|| Fr::zero(), |a, b| a + b);
                    let (lhs, (rhs1, rhs2)) = rayon::join(
                        || Bn254::pairing( sigma.into_affine(), aux.into_affine() ),
                        || rayon::join(
                            || Bn254::pairing(aggregated.into_affine(), kzg.srs.g2[0].into_affine()),
                            || Bn254::pairing((kzg.srs.g1[N + 1] * mu).into_affine(), kzg.srs.g2[0].into_affine())
                        )
                    );
                    lhs == rhs1 + rhs2
                }
            )
        );

        if !verification1 {
            println!("AuthVry failed: aux correctness check failed");
            return false;
        }
        if !verification2 {
            println!("AuthVry failed: aux consistency check failed");
            return false;
        }
        if !verification3 {
            println!("AuthVry failed: pairing equation mismatch");
            return false;
        }
        true
    };

    // Benchmark AuthVry
    let repeat = 500;
    let start = SystemTime::now();
    let vry_results: Vec<(bool, Duration)> = (0..repeat)
        .into_par_iter()
        .map(|i| {
            let start = SystemTime::now();
            let ok = auth_vry(
                db_size,
                &sigma,
                &db,
                &challenge_set,
                &open_proofs,
                &pi_dele,
                &aux,
                &aux1,
                &proof_aux,
                value_aux,
                &r,
            );
            let elapsed = start.elapsed().unwrap_or(Duration::new(0, 0));
            println!(
                "AuthVry Run {}: {}, time: {:.3} ms",
                i + 1,
                if ok { "PASS" } else { "FAIL" },
                elapsed.as_millis() as f64
            );
            (ok, elapsed)
        })
        .collect();
    let elapsed = start.elapsed().unwrap_or(Duration::new(0, 0));

    println!("=== AuthVry Runtime Statistics ===");
    println!("Database size: {}", db_size);
    println!("Total time: {:.3} ms", elapsed.as_millis() as f64);
    println!(
        "Average AuthVry time: {:.3} ms",
        elapsed.as_millis() as f64 / repeat as f64
    );
}

/// Generate random scalar field element
pub fn random_scalar<R: Rng>(rng: &mut R) -> Fr {
    Fr::rand(rng)
}
