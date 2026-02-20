// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

address constant SCHNORR_ADDR = 0x0000000000000000000000000000000000000905;

interface ISchnorr {
	// Verifies a Schnorr signature given the required arguments
	function verify(bytes calldata input) external view returns (bool valid);
}
