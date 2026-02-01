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

//! Traits for handling publish operations in XCM.

use sp_runtime::BoundedVec;
use xcm::latest::{Location, MaxPublishValueLength, PublishKey, PublishTtl, Result as XcmResult};

/// Trait for handling publish operations on the relay chain.
pub trait BroadcastHandler {
	/// Handle publish operation from the given origin.
	/// Publishes a single key-value pair with TTL.
	fn handle_publish(
		origin: &Location,
		key: PublishKey,
		value: BoundedVec<u8, MaxPublishValueLength>,
		ttl: PublishTtl,
	) -> XcmResult;
}

/// Implementation of `BroadcastHandler` for the unit type `()`.
impl BroadcastHandler for () {
	fn handle_publish(
		_origin: &Location,
		_key: PublishKey,
		_value: BoundedVec<u8, MaxPublishValueLength>,
		_ttl: PublishTtl,
	) -> XcmResult {
		Ok(())
	}
}
