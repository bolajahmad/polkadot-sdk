use crate::{
	Config,
	precompiles::{BuiltinAddressMatcher, BuiltinPrecompile, Error, Ext}, vm::RuntimeCosts,
};
use alloc::vec::Vec;
use alloy_core::{
	primitives::Keccak256,
	sol_types::{SolType, sol_data::Bool},
};
use core::{marker::PhantomData, num::NonZero};
use k256::{
	AffinePoint, EncodedPoint, ProjectivePoint, Scalar,
	elliptic_curve::{PrimeField, sec1::FromEncodedPoint},
};
use pallet_revive_uapi::precompiles::schnorr::ISchnorr;
use sp_core::hexdisplay::AsBytesRef;

pub struct Schnorr<T>(PhantomData<T>);

impl<T: Config> BuiltinPrecompile for Schnorr<T> {
	type T = T;
	type Interface = ISchnorr::ISchnorrCalls;
	const MATCHER: BuiltinAddressMatcher =
		BuiltinAddressMatcher::Fixed(NonZero::new(0x905).unwrap());
	const HAS_CONTRACT_INFO: bool = false;

	fn call(
		_address: &[u8; 20],
		input: &Self::Interface,
		env: &mut impl Ext<T = Self::T>,
	) -> Result<Vec<u8>, Error> {
		log::info!("🔐 Schnorr precompile called!");

		fn abi_bool(value: bool) -> Vec<u8> {
			Bool::abi_encode(&value)
		}

		fn lift_even_y_point(x: &[u8]) -> Option<AffinePoint> {
			if x.len() != 32 {
				return None;
			}

			let mut compressed = [0u8; 33];
			compressed[0] = 0x02;
			compressed[1..].copy_from_slice(x);

			let encoded = EncodedPoint::from_bytes(compressed).ok()?;
			Option::<AffinePoint>::from(AffinePoint::from_encoded_point(&encoded))
		}

		use ISchnorr::ISchnorrCalls;

		match input {
			ISchnorrCalls::verify(ISchnorr::verifyCall { input }) => {
				env.frame_meter_mut()
					.charge_weight_token(RuntimeCosts::HashBlake256(input.len() as u32))?;
				// Input must be 128 bytes exactly: pubkey_x || r_x || s || msg.
				if input.len() != 128 {
					return Err(Error::Revert("Invalid input len".into()));
				}
				let input = input.as_bytes_ref();

				let pubkey_x = &input[..32];
				let rx = &input[32..64];
				let s_bytes: [u8; 32] = input[64..96].try_into().unwrap();
				let msg = &input[96..128];

				let pubkey_point = match lift_even_y_point(pubkey_x) {
					Some(pk) => pk,
					None => return Ok(abi_bool(false)),
				};

				let nonce_point = match lift_even_y_point(rx) {
					Some(pk) => pk,
					None => return Ok(abi_bool(false)),
				};

				let s = match Option::<Scalar>::from(Scalar::from_repr(s_bytes.into())) {
					Some(s) => s,
					None => return Ok(abi_bool(false)),
				};

				// Compute the challenge, e
				// We get the tagged_hash
				let mut challenge = Vec::with_capacity(96);
				challenge.extend_from_slice(rx);
				challenge.extend_from_slice(pubkey_x);
				challenge.extend_from_slice(&msg);
				let tag = "PIP/challenge";
				let mut hasher = Keccak256::new();
				hasher.update(tag);
				hasher.update(&challenge);
				let result = hasher.finalize();

				let e = match Option::<Scalar>::from(Scalar::from_repr((*result).into())) {
					Some(e) => e,
					None => return Ok(abi_bool(false)),
				};

				let lhs = ProjectivePoint::GENERATOR * s;
				let rhs =
					ProjectivePoint::from(nonce_point) + (ProjectivePoint::from(pubkey_point) * e);

				if lhs == rhs {
					return Ok(abi_bool(true));
				} else {
					return Ok(abi_bool(false));
				}
			},
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::{
		call_builder::{CallSetup, VmBinaryModule},
		precompiles::Error,
		test_utils::ALICE,
		tests::{ExtBuilder, Test},
	};
	use frame_support::traits::fungible::Mutate;
	use secp256k1::{Parity, PublicKey, Scalar, Secp256k1, SecretKey};
	use crate::precompiles::alloy::sol_types::{SolType, sol_data::Bool};

	fn generate_nonce_key(aux: &[u8; 32], priv_key: &SecretKey, msg: &[u8; 32]) -> SecretKey {
		let secp = Secp256k1::new();

		let mut hasher = Keccak256::new();
		hasher.update("PIP/aux");
		hasher.update(aux);
		let result = hasher.finalize();
		let aux_bytes = *result;

		let t = {
			let mut bytes = [0u8; 32];
			let sk_bytes = priv_key.secret_bytes();
			for i in 0..bytes.len() {
				bytes[i] = aux_bytes[i] ^ sk_bytes[i];
			}
			bytes
		};

		let mut nonce_bytes = Vec::with_capacity(96);
		nonce_bytes.extend_from_slice(&t);
		nonce_bytes.extend_from_slice(msg);
		let mut hasher = Keccak256::new();
		hasher.update("PIP/nonce");
		hasher.update(&nonce_bytes);
		let result = hasher.finalize();
		let nonce_bytes = *result;

		let mut nonce_sk = SecretKey::from_slice(&nonce_bytes).unwrap();
		let (_, parity) = PublicKey::from_secret_key(&secp, &nonce_sk).x_only_public_key();
		if parity == Parity::Odd {
			nonce_sk = nonce_sk.negate();
		}

		nonce_sk
	}

	fn message(text: Option<&str>) -> [u8; 32] {
		let value = text.unwrap_or("Hello, world!");
		let mut hasher = Keccak256::new();
		hasher.update(value);
		hasher.finalize().into()
	}

	fn generate_verify_input(invalid: bool) -> Vec<u8> {
		let secp = Secp256k1::new();

		// Fixed private key
		let mut signer_secret = SecretKey::from_slice(&[1u8; 32]).unwrap();
		let (_, parity) = PublicKey::from_secret_key(&secp, &signer_secret).x_only_public_key();
		if parity == Parity::Odd {
			signer_secret = signer_secret.negate();
		}

		// Deterministic nonce
		let aux = [2u8; 32];
		let nonce_secret = generate_nonce_key(&aux, &signer_secret, &message(None));

		// Get pubkeys
		let nonce_pub = PublicKey::from_secret_key(&secp, &nonce_secret);

		let (signer_xonly, _) =
			PublicKey::from_secret_key(&secp, &signer_secret).x_only_public_key();
		let (nonce_xonly, _) = nonce_pub.x_only_public_key();

		let pubkey_x = signer_xonly.serialize();
		let rx = nonce_xonly.serialize();

		// Compute challenge hash
		let mut challenge = Vec::with_capacity(96);
		challenge.extend_from_slice(&rx);
		challenge.extend_from_slice(&pubkey_x);
		challenge.extend_from_slice(&message(None));
		let mut hasher = Keccak256::new();
		hasher.update("PIP/challenge");
		hasher.update(challenge);
		let digest = hasher.finalize();
		let e = Scalar::from_be_bytes(*digest).unwrap();
		let ed = signer_secret.mul_tweak(&e).expect("e*secret key should be valid");

		let ex_scalar = Scalar::from_be_bytes(ed.secret_bytes()).unwrap();
		let s_secret = nonce_secret.add_tweak(&ex_scalar).expect("k + e*secret should be valid");
		let s = s_secret.secret_bytes();

		// Assemble input bytes
		let mut input = Vec::with_capacity(128);
		input.extend_from_slice(&pubkey_x);
		input.extend_from_slice(&rx);
		input.extend_from_slice(&s);
		input.extend_from_slice(&message(if invalid { Some(&"Mingle") } else { None }));

		println!("Expected Input: {:?}", input);
		input
	}

	#[test]
	fn schnorr_verify_works() {
		ExtBuilder::default().build().execute_with(|| {
			let _ = <Test as Config>::Currency::set_balance(&ALICE, 100_000_000_000);

			let mut call_setup = CallSetup::<Test>::new(VmBinaryModule::evm_sized(1));
			let (mut ext, _) = call_setup.ext();

			let mut call_with = |bytes: Vec<u8>| {
				let input =
					ISchnorr::ISchnorrCalls::verify(ISchnorr::verifyCall { input: bytes.into() });
				let result = Schnorr::<Test>::call(
					&Schnorr::<Test>::MATCHER.base_address(),
					&input,
					&mut ext,
				);
				println!("Result: {:?}", result);
				result
			};

			let err = call_with(vec![0u8; 127]).expect_err("127-byte input should revert");
			assert_eq!(err, Error::Revert("Invalid input len".into()));

			let result =
				call_with(generate_verify_input(false)).expect("valid 128-byte input should work");
			assert_eq!(result.len(), 32, "bool ABI output should be 32 bytes");
			assert_eq!(result, Bool::abi_encode(&true), "Input should match");

			let result = call_with(generate_verify_input(true))
				.expect("invalid 128-byte input should not work");
			assert_eq!(result.len(), 32, "bool ABI output should be 32 bytes");
			assert_eq!(result, Bool::abi_encode(&false), "Input should match");
		})
	}
}
