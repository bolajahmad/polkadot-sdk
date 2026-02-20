use crate::{
	Config,
	precompiles::{BuiltinAddressMatcher, BuiltinPrecompile, Error, Ext},
};
use alloy_core::primitives::Keccak256;
use core::{marker::PhantomData, num::NonZero};
use pallet_revive_uapi::precompiles::schnorr::ISchnorr;
use secp256k1::{Parity, PublicKey, SECP256K1, Scalar, Secp256k1, SecretKey, XOnlyPublicKey};
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
		use ISchnorr::ISchnorrCalls;

		match input {
			ISchnorrCalls::verify(ISchnorr::verifyCall { input }) => {
				// Input must be 192 bytes exactly
				if input.len() != 128 {
					return Err(Error::Revert("Invalid input len".into()));
				}
				let input = input.as_bytes_ref();

				let pubkey_x = &input[..32];
				let rx = &input[32..64];
				let s_bytes = &input[64..96];
				let msg = &input[96..128];

				let secp = Secp256k1::verification_only();

				// Lift public key
				let xonly_pubkey = match XOnlyPublicKey::from_slice(pubkey_x) {
					Ok(pk) => pk,
					Err(_) => return Ok(0_u32.to_le_bytes().to_vec()),
				};
				let pubkey_point = xonly_pubkey.public_key(Parity::Even);

				// Lift nonce key, R
				let xonly_nonce = match XOnlyPublicKey::from_slice(rx) {
					Ok(pk) => pk,
					Err(_) => return Ok(0_u32.to_le_bytes().to_vec()),
				};
				let nonce_point = xonly_nonce.public_key(Parity::Even);

				let s = match Scalar::from_be_bytes(s_bytes.try_into().unwrap()) {
					Ok(s) => s,
					Err(_) => return Ok(0_u32.to_le_bytes().to_vec()),
				};

				// Compute the challenge, e
				// We get the tagged_hash
				let tag = "PIP/challenge";
				let mut hasher = Keccak256::new();
				hasher.update(tag);
				hasher.update(tag);
				hasher.update(rx);
				hasher.update(pubkey_x);
				hasher.update(msg);
				let result = hasher.finalize();

				let e = match Scalar::from_be_bytes(*result) {
					Ok(e) => e,
					Err(_) => return Ok(0_u32.to_le_bytes().to_vec()),
				};

				let sg = PublicKey::from_secret_key(
					&SECP256K1,
					&SecretKey::from_slice(&s.to_be_bytes()).unwrap(),
				);

				let ep = match pubkey_point.mul_tweak(&secp, &e) {
					Ok(p) => p,
					Err(_) => return Ok(0_u32.to_le_bytes().to_vec()),
				};
				let rhs = match nonce_point.combine(&ep) {
					Ok(p) => p,
					Err(_) => return Ok(0_u32.to_le_bytes().to_vec()),
				};

				if sg == rhs {
					return Ok(1_u32.to_le_bytes().to_vec());
				} else {
					return Ok(0_u32.to_le_bytes().to_vec());
				}
			},
		}
	}
}
