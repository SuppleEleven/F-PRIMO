# F-PRIMO: Publicly Verifiable Computation over Multi-Owner Filtered Outsourced Data
 
## Project Introduction
 
F-PRIMO is a publicly verifiable and privacy-preserving computation framework for filtered subsets of multi-owner outsourced databases. Each data owner authenticates their outsourced database through a compact digest, and an untrusted server can generate a concise proof that the output is correctly computed on the owner-authenticated inputs without revealing data or intermediate values.

## Directory Structure

```
F-PRIMO/ 
├── src/ 
│   ├── main.rs        # Main program entry, containing test system 
│   ├── part1.rs       # Protocol part 1 implementation 
│   ├── part2.rs       # Protocol part 2 implementation 
│   ├── ipa.rs         # Inner Product Argument implementation 
│   ├── kzg.rs         # KZG commitment scheme implementation 
│   ├── utils.rs       # Utility functions 
│   ├── types.rs       # Type definitions 
│   └── lib.rs         # Library definition 
├── Cargo.toml         # Project dependency configuration 
├── Cargo.lock         # Dependency version lock 
└── README.md          # Project documentation
```

## Dependencies

The project uses the following main dependencies:
| Dependency | Version | Purpose |
|------|------|------|
| ark-bn254 | 0.4 | BN254 elliptic curve implementation |
| ark-ec | 0.4 | Elliptic curve base library |
| ark-ff | 0.4 | Finite field implementation |
| ark-poly | 0.4 | Polynomial operations |
| ark-std | 0.4 | Standard library extensions |
| ark-serialize | 0.4 | Serialization functionality |
| rand | 0.8 | Random number generation |
| sha2 | 0.10 | Hash function |
| rayon | 1.7 | Parallel computing |
| num_cpus | 1.16 | CPU core detection |

## Core Technology
 
F-PRIMO is built on a new protocol: Commit-and-Prove Zero-Knowledge Proof for Multiple Sets (CP-ZKP-MS), which enables concise proofs for selected subsets across multiple commitment sets while keeping the proof size independent of the number of sets.

Using CP-ZKP-MS, we propose an efficient instantiation of F-PRIMO that supports optimized variants, delegating expensive outsourcing time operations to cloud providers, benefiting lightweight owners.

## Quick Start

### Environment Requirements

- Rust 1.56.0 or higher
- Cargo package manager

### Installation and Running

1. **Clone the Project**

```bash
git clone <repository-url>
cd F-PRIMO
```

2. **Build the Project**

```bash
cargo build --release
```

3. **Run the Main Function**

```bash
./target/release/F-PRIMO | tee test.txt
```
4. **Run the Tests**

```bash
cargo test --lib
```

## Usage

After running the program, you will see the following test mode options:

```
=== CP-ZKP-MS Protocol Test System ===
1. Benchmark Tests
2. Parameterized Tests
3. Standard Commitment Test
4. Delegated Commitment Test
5. Proof Time Test
6. Verification Time Test
Select test mode:
```

### Test Mode Descriptions

1. **Benchmark Tests**：Test the performance of elliptic curve group operations, including G1/G2 addition, scalar multiplication, and pairing operations.

2. **Parameterized Tests**：Test the protocol performance under different parameter combinations.

3. **Standard Commitment Test**：Test the performance of standard vector commitments.

4. **Delegated Commitment Test**：Test the performance of delegated vector commitments.

5. **Proof Performance  Test**：Specifically test the time performance of proof generation.

6. **Verification Performance  Test**：Specifically test the time performance of the verification process.

## Technical Features

1. **Input-sensitive efficiency**: Communication and verification costs depend only on the actual data items participating in the computation
2. **Parallel computation**: Uses Rayon library to implement parallel computation for improved performance
3. **Efficient implementation**: Optimized elliptic curve operations and polynomial calculations
4. **Modular design**: Clear code structure for easy maintenance and extension
5. **Comprehensive testing**: Multiple test modes covering different scenarios
6. **Detailed performance analysis**: Provides detailed time statistics and performance metrics
7. **Security**: Proven secure in the algebraic group model

## Application Scenarios
 
F-PRIMO is suitable for the following scenarios:
 
- **Multi-owner data outsourcing**: Multiple data owners outsource data to cloud service providers
- **Data privacy protection**: Perform computations without revealing original data
- **Computation result verification**: Verify the correctness of computation results from cloud service providers
- **Large-scale data analysis**: Support large-scale multi-owner outsourced data analysis
 
## Security Guarantees
 
F-PRIMO  is proven secure in the algebraic group model, ensuring:
 
- **Data privacy**: Does not reveal original data or intermediate calculation values
- **Computation correctness**: Ensures the correctness of computation results
- **Data authentication**: Verifies that data comes from legitimate owners
- **Unforgeability**: Attackers cannot forge valid proofs
