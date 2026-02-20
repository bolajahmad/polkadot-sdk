//! Information around the `Schnorr` pre-compile.

pub const SCHNORR_PRECOMPILE_ADDR: [u8; 20] =
	hex_literal::hex!("0000000000000000000000000000000000000905");

#[cfg(feature = "precompiles-sol-interfaces")]
alloy_core::sol!("sol/ISchnorr.sol");
