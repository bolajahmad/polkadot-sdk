// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

//! Configuration of the statement protocol

use std::time;

/// Interval at which we propagate statements;
pub(crate) const PROPAGATE_TIMEOUT: time::Duration = time::Duration::from_millis(1000);

/// Maximum number of known statement hashes to keep for a peer.
pub const MAX_KNOWN_STATEMENTS: usize = 4 * 1024 * 1024; // * 32 bytes for hash = 128 MB per peer

/// Maximum allowed size for a statement notification.
pub const MAX_STATEMENT_NOTIFICATION_SIZE: u64 = 1024 * 1024;

/// Maximum number of statement validation request we keep at any moment.
pub const MAX_PENDING_STATEMENTS: usize = 2 * 1024 * 1024;

/// Maximum statements in a 10-second sliding window before punishment.
pub const MAX_STATEMENTS_PER_WINDOW: u32 = 500_000;

/// Sliding window duration for flood detection.
pub const RATE_LIMIT_WINDOW_DURATION: time::Duration = time::Duration::from_secs(10);
