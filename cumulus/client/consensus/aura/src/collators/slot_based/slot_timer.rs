// Copyright (C) Parity Technologies (UK) Ltd.
// This file is part of Cumulus.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// Cumulus is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Cumulus is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Cumulus. If not, see <https://www.gnu.org/licenses/>.

use crate::LOG_TARGET;
use cumulus_primitives_aura::Slot;
use sc_consensus_aura::SlotDuration;
use sp_timestamp::Timestamp;
use std::time::Duration;

#[derive(Debug)]
pub(crate) struct SlotInfo {
	pub timestamp: Timestamp,
	pub slot: Slot,
}

/// Information about a slot timing, including the slot duration and exact start timestamp.
#[derive(Debug, Clone)]
pub(crate) struct SlotTime {
	/// The slot duration used for this timing
	slot_duration: Duration,
	/// The exact timestamp when this slot started
	slot_start_timestamp: Timestamp,
	/// Time offset to apply when calculating time remaining
	time_offset: Duration,
}

impl SlotTime {
	/// Create a new SlotTime
	pub fn new(
		slot_duration: Duration,
		slot_start_timestamp: Timestamp,
		time_offset: Duration,
	) -> Self {
		Self { slot_duration, slot_start_timestamp, time_offset }
	}

	/// Get the time remaining in this slot
	pub fn time_left(&self) -> Duration {
		self.time_left_internal(duration_now())
	}

	/// Internal implementation of [`Self::time_left`] that takes `now` as parameter.
	fn time_left_internal(&self, now: Duration) -> Duration {
		let now = now.saturating_sub(self.time_offset);
		let slot_end_time_millis =
			self.slot_start_timestamp.as_millis() + self.slot_duration.as_millis() as u64;
		let slot_end_time = Duration::from_millis(slot_end_time_millis);

		slot_end_time.saturating_sub(now)
	}

	/// Check if the next relay chain slot would be in a different parachain slot.
	pub fn is_parachain_slot_ending(&self, parachain_slot_duration: Duration) -> bool {
		let now = duration_now().saturating_sub(self.time_offset);
		let next_relay_slot_start_time =
			self.slot_start_timestamp.as_duration() + self.slot_duration;

		// Calculate current parachain slot
		let current_parachain_slot = now.as_millis() / parachain_slot_duration.as_millis();

		// Calculate parachain slot for next relay slot
		let next_parachain_slot =
			next_relay_slot_start_time.as_millis() / parachain_slot_duration.as_millis() as u128;

		current_parachain_slot != next_parachain_slot
	}
}

/// Manages block-production slots based on the relay chain slot duration.
#[derive(Debug)]
pub(crate) struct SlotTimer {
	/// Offset the current time by this duration.
	time_offset: Duration,
	/// Slot duration of the relay chain. This is used to compute when to wake up for
	/// block production attempts.
	relay_slot_duration: Duration,
	/// Stores the latest slot that was reported by [`Self::wait_until_next_slot`].
	last_reported_slot: Option<Slot>,
}

/// Returns current duration since Unix epoch.
fn duration_now() -> Duration {
	use std::time::SystemTime;
	let now = SystemTime::now();
	now.duration_since(SystemTime::UNIX_EPOCH).unwrap_or_else(|e| {
		panic!("Current time {:?} is before Unix epoch. Something is wrong: {:?}", now, e)
	})
}

<<<<<<< HEAD
/// Returns the duration until the next block production slot and the timestamp at this slot.
fn time_until_next_slot(
||||||| 9972470602d
/// Adjust the authoring duration.
fn adjust_authoring_duration(
	mut authoring_duration: Duration,
	next_block: (Duration, Slot),
	next_slot_change: (Duration, Slot),
	different_authors: bool,
) -> Option<Duration> {
	let (duration, next_block_slot) = next_block;
	let (duration_until_next_slot, next_slot) = next_slot_change;

	// The authoring of blocks must stop 1 second before the slot ends.
	let duration_until_deadline =
		duration_until_next_slot.saturating_sub(BLOCK_PRODUCTION_ADJUSTMENT_MS);
	tracing::debug!(
		target: LOG_TARGET,
		?authoring_duration,
		?duration,
		?next_block_slot,
		?duration_until_next_slot,
		?next_slot,
		?duration_until_deadline,
		?different_authors,
		"Adjusting authoring duration for slot.",
	);

	// Ensure no blocks are produced in the last second of the slot,
	// regardless of authoring duration.
	if duration_until_deadline == Duration::ZERO {
		if different_authors {
			tracing::warn!(
				target: LOG_TARGET,
				?duration_until_next_slot,
				?next_slot,
				"Not enough time left in the slot to adjust authoring duration. Skipping block production for the slot."
			);

			return None;
		}

		// If authors are the same, we can still attempt producing the block
		// considering the next block duration.
		return Some(authoring_duration.min(duration));
	}

	// Clamp the authoring duration to fit into the slot deadline only if authors are different.
	// For most cases, the deadline is farther in the future than the authoring duration.
	if different_authors && authoring_duration >= duration_until_deadline {
		authoring_duration = duration_until_deadline;

		// Ensure we are not going below the minimum interval within a reasonable threshold.
		// For 12 cores, we might have a scenario where the last 3 blocks are skipped:
		// - Block 10: next slot change in 1.493s:
		// 	 - After adjusting the deadline: 1.493s - 1s = 0.493s the block could be produced
		//     without issues.
		// - Block 11: next slot change in 0.993s - skipped by the deadline
		// - Block 12: next slot change in 0.493s - skipped by the deadline
		if authoring_duration <
			BLOCK_PRODUCTION_MINIMUM_INTERVAL_MS.saturating_sub(BLOCK_PRODUCTION_THRESHOLD_MS)
		{
			tracing::debug!(
				target: LOG_TARGET,
				?authoring_duration,
				?next_slot,
				"Authoring duration is below minimum. Skipping block production for the slot."
			);
			return None;
		}
	}

	// The `duration` intends to slightly adjust when then block production
	// attempt happens. This goes slightly below the `BLOCK_PRODUCTION_MINIMUM_INTERVAL_MS`
	// threshold.
	Some(authoring_duration.min(duration))
}

/// Returns the duration until the next block production should be attempted.
fn time_until_next_attempt(
	now: Duration,
	block_production_interval: Duration,
	offset: Duration,
) -> (Duration, Timestamp) {
	let now = now.saturating_sub(offset).as_millis();

	let next_slot_time = ((now + block_production_interval.as_millis()) /
		block_production_interval.as_millis()) *
		block_production_interval.as_millis();
	let remaining_millis = next_slot_time - now;
	(Duration::from_millis(remaining_millis as u64), Timestamp::from(next_slot_time as u64))
}

impl SlotTimer {
	/// Create a new slot timer.
	pub fn new_with_offset(time_offset: Duration, relay_slot_duration: Duration) -> Self {
		Self { time_offset, relay_slot_duration, last_reported_slot: None }
	}

	/// Returns a future that resolves when the next block production should be attempted.
	pub async fn wait_until_next_slot(&mut self) -> Result<SlotTime, ()> {
		let (time_until_next_attempt, timestamp) =
			time_until_next_slot(duration_now(), self.relay_slot_duration, self.time_offset);

		// Calculate the current slot using the relay chain slot duration
		let relay_slot_duration_for_slot = SlotDuration::from(self.relay_slot_duration);
		let mut current_slot = Slot::from_timestamp(timestamp, relay_slot_duration_for_slot);

		// Calculate the actual slot start timestamp (may be different if we're catching up)
		let mut slot_start_timestamp = timestamp;

		match self.last_reported_slot {
			// If we already reported a slot, we don't want to skip a slot. But we also don't want
			// to go through all the slots if a node was halted for some reason.
			Some(ls) if ls + 1 < current_slot && current_slot <= ls + 3 => {
				current_slot = ls + 1u64;
				// Calculate the timestamp for the adjusted slot
				slot_start_timestamp =
					current_slot.timestamp(relay_slot_duration_for_slot).ok_or(())?;
				// Don't sleep since we're catching up
				tracing::debug!(
					target: LOG_TARGET,
					last_slot = ?ls,
					current_slot = ?current_slot,
					"Catching up on skipped slot."
				);
			},
			None | Some(_) => {
				tracing::trace!(
					target: LOG_TARGET,
					time_to_sleep = ?time_until_next_attempt,
					"Feeling sleepy 😴"
				);

				// Sleep based on relay chain timing
				tokio::time::sleep(time_until_next_attempt).await;
			},
		}

		tracing::debug!(
			target: LOG_TARGET,
			relay_slot_duration = ?self.relay_slot_duration,
			?current_slot,
			?slot_start_timestamp,
			"New block production slot."
		);

		// Update internal slot tracking
		self.last_reported_slot = Some(current_slot);

		Ok(SlotTime::new(self.relay_slot_duration, slot_start_timestamp, self.time_offset))
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use rstest::rstest;
	const RELAY_CHAIN_SLOT_DURATION: u64 = 6000;

	#[rstest]
	// Test that different now timestamps have correct impact
	#[case(1000, 0, 5000)]
	#[case(0, 0, 6000)]
	#[case(6000, 0, 6000)]
	// Test that offset affects the current time correctly
	#[case(1000, 1000, 6000)]
	#[case(12000, 2000, 2000)]
	#[case(12000, 6000, 6000)]
	#[case(12000, 7000, 1000)]
	// Test basic timing with relay slot duration
	#[case(11999, 0, 1)]
	fn test_get_next_slot(
		#[case] time_now: u64,
		#[case] offset_millis: u64,
		#[case] expected_wait_duration: u128,
	) {
		let relay_slot_duration = Duration::from_millis(RELAY_CHAIN_SLOT_DURATION);
		let time_now = Duration::from_millis(time_now);
		let offset = Duration::from_millis(offset_millis);

		let (wait_duration, _) = time_until_next_slot(time_now, relay_slot_duration, offset);

		assert_eq!(wait_duration.as_millis(), expected_wait_duration, "Wait time mismatch.");
	}

	#[rstest]
	// Basic slot change scenarios
	#[case(6000, 0, 0, Slot::from(0), 6000)]
	#[case(6000, 1000, 0, Slot::from(0), 5000)]
	#[case(6000, 6000, 0, Slot::from(1), 6000)]
	#[case(6000, 12000, 0, Slot::from(2), 6000)]
	// Test with offset
	#[case(6000, 1000, 1000, Slot::from(0), 6000)]
	#[case(6000, 2000, 1000, Slot::from(0), 5000)]
	#[case(6000, 6000, 3000, Slot::from(0), 3000)]
	// Different slot durations
	#[case(3000, 1000, 0, Slot::from(0), 2000)]
	#[case(3000, 3000, 0, Slot::from(1), 3000)]
	#[case(12000, 6000, 0, Slot::from(0), 6000)]
	#[case(12000, 12000, 0, Slot::from(1), 12000)]
	// Edge cases - at slot boundary
	#[case(6000, 5999, 0, Slot::from(0), 1)]
	#[case(6000, 11999, 0, Slot::from(1), 1)]
	fn test_compute_time_until_next_slot_change(
		#[case] para_slot_millis: u64,
		#[case] time_now: u64,
		#[case] offset_millis: u64,
		#[case] last_reported_slot: Slot,
		#[case] expected_duration: u128,
	) {
		let slot_time = SlotTime {
			slot_duration: Duration::from_millis(para_slot_millis),
			time_offset: Duration::from_millis(offset_millis),
			slot_start_timestamp: Timestamp::new(
				Duration::from_millis(para_slot_millis).as_millis() as u64 * *last_reported_slot,
			),
		};

		let time_left = slot_time.time_left_internal(Duration::from_millis(time_now));

		assert_eq!(time_left.as_millis(), expected_duration, "Duration mismatch");
	}
}
