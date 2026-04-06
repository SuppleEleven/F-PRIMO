use ark_bn254::{Bn254, Fr, G1Affine, G2Affine, Gt};  
use ark_ec::{models::short_weierstrass::Affine, CurveGroup, Group};
use ark_ff::{Field, PrimeField}; 
use ark_std::vec::Vec;

type G1 = <Bn254 as ark_ec::pairing::Pairing>::G1; 
type G2 = <Bn254 as ark_ec::pairing::Pairing>::G2;  

type CommitmentG1 = G1;  
type G2Commitment = G2;
type CommitmentGt = Gt;  

type VecFr = Vec<Fr>;  
type PolyFr = ark_poly::univariate::DensePolynomial<Fr>; 