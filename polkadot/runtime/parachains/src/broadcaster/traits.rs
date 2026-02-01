// Copyright (C) Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.

//! Traits for publish operations in the broadcaster pallet.

use alloc::vec::Vec;
use polkadot_primitives::Id as ParaId;
use sp_runtime::DispatchResult;

/// Trait for handling publish operations for parachains.
pub trait Publish {
	/// Publish a single key-value pair with TTL for a specific parachain.
	///
	/// - key: 32-byte hash
	/// - value: raw bytes
	/// - ttl: blocks until expiration (0 = infinite/never expires)
	fn publish_data(publisher: ParaId, key: [u8; 32], value: Vec<u8>, ttl: u32) -> DispatchResult;
}
