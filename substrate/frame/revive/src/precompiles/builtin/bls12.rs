// This file is not really part of Substrate.

// Copyright (C) bolajahmad.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use crate::{
	Config,
	precompiles::{BuiltinAddressMatcher, Error, Ext, PrimitivePrecompile},
	vm::RuntimeCosts,
};
use alloc::vec::Vec;
use alloy_core::sol_types::SolValue;
use ark_bls12_381::{Fq, Fq2, Fr, G1Affine, G1Projective, G2Affine, G2Projective};
use ark_ec::{AffineRepr, CurveGroup, VariableBaseMSM};
use ark_ff::{BigInteger, PrimeField, Zero};
use core::{marker::PhantomData, num::NonZero};
use sp_runtime::DispatchError;

/// Size of a single coordinate in EIP-2537 encoding (64 bytes, big-endian, zero-padded).
const FP_LENGTH: usize = 64;
/// Size of a G1 point in EIP-2537 encoding (128 bytes = 2 coordinates).
const G1_LENGTH: usize = 128;
/// Actual byte size of a BLS12-381 field element (48 bytes).
const FP_ACTUAL_SIZE: usize = 48;
/// Padding bytes at the start of each coordinate (16 bytes of zeros).
const FP_PAD_SIZE: usize = FP_LENGTH - FP_ACTUAL_SIZE;

/// Decode a field element (Fq) from 64-byte big-endian EIP-2537 encoding.
///
/// The first 16 bytes must be zeros (padding), followed by 48 bytes of the actual field element.
fn decode_fp(input: &[u8]) -> Result<Fq, DispatchError> {
	if input.len() != FP_LENGTH {
		return Err(DispatchError::from("Invalid field element length"));
	}

	// Check that padding 16-bytes are zeros
	if input[..FP_PAD_SIZE].iter().any(|&b| b != 0) {
		return Err(DispatchError::from("Invalid padding bytes"));
	}

	// The actual field element is in the last 48 bytes, big-endian
	// ark_ff expects little-endian, so we need to reverse
	let mut le_bytes = [0u8; FP_ACTUAL_SIZE];
	le_bytes.copy_from_slice(&input[FP_PAD_SIZE..]);
	le_bytes.reverse();

	Fq::from_bigint(ark_ff::BigInt::new(core::array::from_fn(|i| {
		let start = i * 8;
		u64::from_le_bytes(le_bytes[start..start + 8].try_into().unwrap())
	})))
	.ok_or_else(|| DispatchError::from("Invalid field element"))
}

/// Decode a G1 point from 128-byte EIP-2537 encoding.
///
/// Input format: 64 bytes for x-coordinate || 64 bytes for y-coordinate
/// Returns the point at infinity if both coordinates are zero.
fn decode_g1(input: &[u8]) -> Result<G1Affine, DispatchError> {
	if input.len() != G1_LENGTH {
		return Err(DispatchError::from("Invalid G1 point length"));
	}

	let x = decode_fp(&input[..FP_LENGTH])?;
	let y = decode_fp(&input[FP_LENGTH..])?;

	// Check for point at infinity (both coordinates zero)
	if x.is_zero() && y.is_zero() {
		return Ok(G1Affine::identity());
	}

	// Construct the affine point and validate it's on the curve
	let point = G1Affine::new(x, y);
	if !point.is_on_curve() {
		return Err(DispatchError::from("Point not on curve"));
	}

	Ok(point)
}

/// Encode a G1 point to 128-byte EIP-2537 format.
fn encode_g1(point: &G1Affine) -> [u8; G1_LENGTH] {
	let mut result = [0u8; G1_LENGTH];

	if point.is_zero() {
		// Point at infinity - return all zeros
		return result;
	}

	// Encode x coordinate (big-endian, zero-padded to 64 bytes)
	let x_bytes = point.x().unwrap().into_bigint().to_bytes_be();
	result[FP_PAD_SIZE..FP_LENGTH].copy_from_slice(&x_bytes);

	// Encode y coordinate (big-endian, zero-padded to 64 bytes)
	let y_bytes = point.y().unwrap().into_bigint().to_bytes_be();
	result[FP_LENGTH + FP_PAD_SIZE..].copy_from_slice(&y_bytes);

	result
}

pub struct BLS12G1Add<T>(PhantomData<T>);

impl<T: Config> PrimitivePrecompile for BLS12G1Add<T> {
	type T = T;
	const MATCHER: BuiltinAddressMatcher =
		BuiltinAddressMatcher::Fixed(NonZero::new(0x0b).unwrap());
	const HAS_CONTRACT_INFO: bool = false;

	/// BLS12_G1ADD precompile (EIP-2537).
	///
	/// Input: 256 bytes representing two G1 points (128 bytes each).
	/// Output: 128 bytes representing the sum of the two points.
	fn call(
		_address: &[u8; 20],
		input: Vec<u8>,
		env: &mut impl Ext<T = Self::T>,
	) -> Result<Vec<u8>, Error> {
		// TODO: add proper benchmarking and weight charging for this precompile.
		env.frame_meter_mut().charge_weight_token(RuntimeCosts::Bn128Add)?;

		if input.len() != 256 {
			return Err(Error::Revert("Invalid input length".into()));
		}

		// Decode the two G1 points
		let p1 =
			decode_g1(&input[..G1_LENGTH]).map_err(|_| Error::Revert("Invalid G1 point".into()))?;
		let p2 =
			decode_g1(&input[G1_LENGTH..]).map_err(|_| Error::Revert("Invalid G1 point".into()))?;

		// Perform point addition in projective coordinates and convert back to affine
		let sum = (G1Projective::from(p1) + G1Projective::from(p2)).into_affine();

		// Encode the result
		let result = encode_g1(&sum);
		println!("G1 Add Result, {:?}", result);
		Ok(result.to_vec())
	}
}

const G1_MSM_SLICE_SIZE: usize = 160;
/// Scalar size in EIP-2537 encoding (32 bytes, big-endian).
const SCALAR_LENGTH: usize = 32;

/// Decode a scalar field element (Fr) from 32-byte big-endian encoding.
fn decode_scalar(input: &[u8]) -> Result<Fr, DispatchError> {
	if input.len() != SCALAR_LENGTH {
		return Err(DispatchError::from("Invalid scalar length"));
	}

	// EIP-2537 scalars are big-endian, ark_ff expects little-endian
	let mut le_bytes = [0u8; SCALAR_LENGTH];
	le_bytes.copy_from_slice(input);
	le_bytes.reverse();

	// Use from_le_bytes_mod_order which reduces modulo the scalar field order
	Ok(Fr::from_le_bytes_mod_order(&le_bytes))
}

pub struct BLS12G1MSM<T>(PhantomData<T>);

impl<T: Config> PrimitivePrecompile for BLS12G1MSM<T> {
	type T = T;
	const MATCHER: BuiltinAddressMatcher =
		BuiltinAddressMatcher::Fixed(NonZero::new(0x0c).unwrap());
	const HAS_CONTRACT_INFO: bool = false;

	/// BLS12_G1MSM precompile (EIP-2537).
	/// Inputs: (160 * k)-bytes representing k pairs of (G1 point, scalar).
	/// Each pair consists of a 128-byte G1 point followed by a
	/// 32-byte scalar.
	fn call(
		_address: &[u8; 20],
		input: Vec<u8>,
		env: &mut impl Ext<T = Self::T>,
	) -> Result<Vec<u8>, Error> {
		// TODO: add proper benchmarking and weight charging for this precompile.
		env.frame_meter_mut().charge_weight_token(RuntimeCosts::Bn128Add)?;

		if input.is_empty() || input.len() % G1_MSM_SLICE_SIZE != 0 {
			return Err(Error::Revert("Invalid input length".into()));
		}
		let k = input.len() / G1_MSM_SLICE_SIZE;

		let mut points = Vec::with_capacity(k);
		let mut scalars = Vec::with_capacity(k);

		for chunk in input.chunks_exact(G1_MSM_SLICE_SIZE) {
			let point = decode_g1(&chunk[..G1_LENGTH])
				.map_err(|_| Error::Revert("Invalid G1 point".into()))?;
			let scalar = decode_scalar(&chunk[G1_LENGTH..])
				.map_err(|_| Error::Revert("Invalid scalar".into()))?;

			points.push(point);
			scalars.push(scalar);
		}

		// Use arkworks VariableBaseMSM for multi-scalar multiplication
		let result = G1Projective::msm(&points, &scalars)
			.map(|p| p.into_affine())
			.map_err(|_| Error::Revert("MSM computation failed".into()))?;

		Ok(encode_g1(&result).to_vec())
	}
}

/// Size of a single coordinate in EIP-2537 encoding (64 bytes, big-endian, zero-padded).
const FP2_LENGTH: usize = 128;
/// Size of a G1 point in EIP-2537 encoding (128 bytes = 2 coordinates).
const G2_LENGTH: usize = 256;
/// Actual byte size of a BLS12-381 field element (48 bytes).
const FP2_ACTUAL_SIZE: usize = 96;
/// Padding bytes at the start of each coordinate (16 bytes of zeros).
const FP2_PAD_SIZE: usize = FP2_LENGTH - FP2_ACTUAL_SIZE;

fn decode_fp2(input: &[u8]) -> Result<Fq2, DispatchError> {
	if input.len() != FP2_LENGTH {
		return Err(DispatchError::from("Invalid Fp2 length"));
	}

	let c1 = decode_fp(&input[..64])?;
	let c0 = decode_fp(&input[64..])?;

	Ok(Fq2::new(c0, c1))
}

fn decode_g2(input: &[u8]) -> Result<G2Affine, DispatchError> {
	if input.len() != G2_LENGTH {
		return Err(DispatchError::from("Invalid G2 length"));
	}

	let x = decode_fp2(&input[..FP2_LENGTH])?;
	let y = decode_fp2(&input[FP2_LENGTH..])?;

	if x.is_zero() && y.is_zero() {
		return Ok(G2Affine::identity());
	}

	let point = G2Affine::new(x, y);
	if !point.is_on_curve() {
		return Err(DispatchError::from("Point not on curve"));
	}

	Ok(point)
}

fn encode_fp(value: &Fq) -> [u8; FP_LENGTH] {
	let mut out = [0u8; FP_LENGTH];

	// Convert field element to little endian bytes
	let mut le_bytes = value.into_bigint().to_bytes_le();

	// Ensure exactly 48 bytes
	le_bytes.resize(FP_ACTUAL_SIZE, 0);

	// Convert to big endian
	le_bytes.reverse();

	// Copy into padded area
	out[FP_PAD_SIZE..].copy_from_slice(&le_bytes);

	out
}

fn encode_fp2(point: &Fq2) -> [u8; FP2_LENGTH] {
	let mut out = [0u8; FP2_LENGTH];

	let c1_bytes = encode_fp(&point.c1);
	let c0_bytes = encode_fp(&point.c0);

	out[..64].copy_from_slice(&c1_bytes);
	out[64..].copy_from_slice(&c0_bytes);

	out
}

pub fn encode_g2(point: &G2Affine) -> [u8; G2_LENGTH] {
	let mut out = [0u8; G2_LENGTH];

	// infinity encoding
	if point.x.is_zero() && point.y.is_zero() {
		return out;
	}

	let x_bytes = encode_fp2(&point.x);
	let y_bytes = encode_fp2(&point.y);

	out[..FP2_LENGTH].copy_from_slice(&x_bytes);
	out[FP2_LENGTH..].copy_from_slice(&y_bytes);

	out
}

pub struct BLS12G2Add<T>(PhantomData<T>);

impl<T: Config> PrimitivePrecompile for BLS12G2Add<T> {
	type T = T;
	const MATCHER: BuiltinAddressMatcher =
		BuiltinAddressMatcher::Fixed(NonZero::new(0x0d).unwrap());
	const HAS_CONTRACT_INFO: bool = false;

	fn call(
		_address: &[u8; 20],
		input: Vec<u8>,
		env: &mut impl Ext<T = Self::T>,
	) -> Result<Vec<u8>, Error> {
		// TODO: add proper benchmarking and weight charging for this precompile.
		env.frame_meter_mut().charge_weight_token(RuntimeCosts::Bn128Add)?;

		if input.len() != 512 {
			return Err(Error::Revert("Invalid input length".into()));
		}

		// Decode the two G1 points
		let p1 =
			decode_g2(&input[..G2_LENGTH]).map_err(|_| Error::Revert("Invalid G2 point".into()))?;
		let p2 =
			decode_g2(&input[G2_LENGTH..]).map_err(|_| Error::Revert("Invalid G2 point".into()))?;

		// Perform point addition in projective coordinates and convert back to affine
		let sum = (G2Projective::from(p1) + G2Projective::from(p2)).into_affine();

		// Encode the result
		let result = encode_g2(&sum);
		println!("G12` Add Result, {:?}", result);
		Ok(result.to_vec())
	}
}

const G2_MSM_SLICE_SIZE: usize = 288;

pub struct BLS12G2MSM<T>(PhantomData<T>);

impl<T: Config> PrimitivePrecompile for BLS12G2MSM<T> {
	type T = T;
	const MATCHER: BuiltinAddressMatcher =
		BuiltinAddressMatcher::Fixed(NonZero::new(0x0e).unwrap());
	const HAS_CONTRACT_INFO: bool = false;

	fn call(
		_address: &[u8; 20],
		input: Vec<u8>,
		env: &mut impl Ext<T = Self::T>,
	) -> Result<Vec<u8>, Error> {
		// TODO: add proper benchmarking and weight charging for this precompile.
		env.frame_meter_mut().charge_weight_token(RuntimeCosts::Bn128Add)?;

		if input.is_empty() || input.len() % G1_MSM_SLICE_SIZE != 0 {
			return Err(Error::Revert("Invalid input length".into()));
		}
		let k = input.len() / G2_MSM_SLICE_SIZE;

		let mut points = Vec::with_capacity(k);
		let mut scalars = Vec::with_capacity(k);

		for chunk in input.chunks_exact(G2_MSM_SLICE_SIZE) {
			let point = decode_g2(&chunk[..G2_LENGTH])
				.map_err(|_| Error::Revert("Invalid G2 point".into()))?;
			let scalar = decode_scalar(&chunk[G2_LENGTH + 256..])
				.map_err(|_| Error::Revert("Invalid scalar".into()))?;

			points.push(point);
			scalars.push(scalar);
		}

		let result = G2Projective::msm(&points, &scalars)
			.map(|p| p.into_affine())
			.map_err(|_| Error::Revert("MSM computation failed".into()))?;

		Ok(encode_g2(&result).to_vec())
	}
}

#[cfg(test)]
mod tests {
	use crate::{
		precompiles::tests::{run_failure_test_vectors, run_test_vectors},
		tests::Test,
	};

	use super::*;

	#[test]
	fn test_bls12381_g1_add() {
		run_test_vectors::<BLS12G1Add<Test>>(include_str!("./testdata/11-bls12381.json"));
	}

	#[test]
	fn test_bls12381_g1_msm() {
		run_test_vectors::<BLS12G1MSM<Test>>(include_str!("./testdata/12-bls12381G1msm.json"));
	}

	#[test]
	fn test_bls12381_g2_add() {
		run_test_vectors::<BLS12G2Add<Test>>(include_str!("./testdata/13-bls12381_g2_add.json"));
	}

	#[test]
	fn test_bls12381_g2_msm() {
		run_test_vectors::<BLS12G2MSM<Test>>(include_str!("./testdata/14-bls12381_g2_msm.json"));
	}
}
