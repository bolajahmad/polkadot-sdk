use super::{Error, Hash, IsPruned, LastCanonicalized, NomtOverlay, PruningMode, StateDbError};
use parking_lot::{Condvar, Mutex, RwLock};
use sp_database::NomtChanges;
use std::{
	collections::{HashMap, VecDeque},
	sync::{Arc, Weak},
};

pub struct StateDb<BlockHash: Hash> {
	pub(super) mode: PruningMode,
	last_canonicalized: Option<(BlockHash, u64)>,
	levels: VecDeque<OverlayLevel<BlockHash>>,
	parents: HashMap<BlockHash, BlockHash>,
	canonicalization_lock: Arc<Mutex<()>>,
	_phantom: core::marker::PhantomData<BlockHash>,
}

#[cfg_attr(test, derive(PartialEq, Debug))]
struct OverlayLevel<BlockHash: Hash> {
	blocks: Vec<(BlockHash, Arc<NomtOverlay>)>,
}

impl<BlockHash: Hash> StateDb<BlockHash> {
	pub(super) fn new(mode: PruningMode) -> Self {
		Self {
			mode,
			levels: VecDeque::new(),
			parents: HashMap::new(),
			last_canonicalized: None,
			canonicalization_lock: Arc::new(Mutex::new(())),
			_phantom: core::marker::PhantomData::default(),
		}
	}

	// NOTE: this code assumes that if there is at least one element within
	// the parents map with the key parent_hash, then it is okay to be
	// inserted at the level, but there are no checks that the parent is exactly
	// within the previous level. Should this be done?
	pub(super) fn insert_block(
		&mut self,
		hash: &BlockHash,
		number: u64,
		parent_hash: &BlockHash,
		overlay: NomtOverlay,
	) -> Result<(), StateDbError> {
		let front_block_number = self.front_block_number();

		if self.levels.is_empty() && self.last_canonicalized.is_none() && number > 0 {
			// TODO: handle case where number > 0 but overlays is empty,
			// number - 1 should be assumed to be the last canonicalized.
			todo!()
		} else if self.last_canonicalized.is_some() {
			if number < front_block_number || number > front_block_number + self.levels.len() as u64
			{
				return Err(StateDbError::InvalidBlockNumber)
			}

			if number == front_block_number {
				if !self
					.last_canonicalized
					.as_ref()
					.map_or(false, |&(ref h, n)| h == parent_hash && n == number - 1)
				{
					return Err(StateDbError::InvalidParent)
				}
			} else if !self.parents.contains_key(parent_hash) {
				return Err(StateDbError::InvalidParent)
			}
		}

		let level = if self.levels.is_empty() ||
			number == front_block_number + self.levels.len() as u64
		{
			self.levels.push_back(OverlayLevel { blocks: vec![] });
			self.levels.back_mut().expect("can't be empty after insertion; qed")
		} else {
			self.levels.get_mut((number - front_block_number) as usize)
				.expect("number is [front_block_number .. front_block_number + levels.len()) is asserted in precondition; qed")
		};

		level.blocks.push((hash.clone(), Arc::new(overlay)));
		self.parents.insert(hash.clone(), parent_hash.clone());

		Ok(())
	}

	fn front_block_number(&self) -> u64 {
		self.last_canonicalized.as_ref().map(|&(_, n)| n + 1).unwrap_or(0)
	}

	pub(super) fn canonicalize_block(
		&mut self,
		hash: &BlockHash,
	) -> Result<NomtChanges, StateDbError> {
		let guard = self.canonicalization_lock.lock_arc();

		let Some(level) = self.levels.pop_front() else { return Err(StateDbError::InvalidBlock) };

		// Ensure that the blocks that need to be canonicalized are present within the front level.
		if !level.blocks.iter().any(|(block_hash, _)| block_hash == hash) {
			return Err(StateDbError::InvalidBlock)
		}

		// NOTE: this code keeps alive overlays which are built on discarded blocks.
		let mut canonicalized_overlay = None;
		for (overlay_hash, overlay) in level.blocks.into_iter() {
			if hash == &overlay_hash {
				canonicalized_overlay = Some(overlay);
			} else {
				self.parents.remove(&overlay_hash);
			}
		}

		self.last_canonicalized = Some((hash.clone(), self.front_block_number()));
		// UNWRAP: It has already been confirmed that the overlay is present.
		Ok(NomtChanges { overlay: canonicalized_overlay.unwrap(), _canonicalization_guard: guard })
	}

	pub(super) fn last_canonicalized(&self) -> LastCanonicalized {
		self.last_canonicalized
			.as_ref()
			.map(|&(_, n)| LastCanonicalized::Block(n))
			.unwrap_or(LastCanonicalized::None)
	}

	pub(super) fn is_pruned(&self, hash: &BlockHash, number: u64) -> IsPruned {
		let Some((last_canonicalized_hash, last_canonicalized_number)) =
			self.last_canonicalized.as_ref()
		else {
			return IsPruned::NotPruned
		};

		if number < *last_canonicalized_number {
			IsPruned::Pruned
		} else if (&number == last_canonicalized_number && hash == last_canonicalized_hash) ||
			self.parents.contains_key(hash)
		{
			IsPruned::NotPruned
		} else {
			// There could be overlays which have a discarted ancestor.
			// Should they be considered pruned or not?
			todo!()
		}
	}

	pub fn wait_for_canonicalization(&self) {
		if self.canonicalization_lock.is_locked() {
			let _guard = self.canonicalization_lock.lock();
		}
	}

	pub fn overlays(&self, hash: &BlockHash) -> Result<Vec<Arc<NomtOverlay>>, StateDbError> {
		let mut overlays = vec![];

		if self.last_canonicalized.as_ref().map_or(false, |(h, _)| h == hash) {
			return Ok(overlays)
		}

		let mut next_hash = hash;
		for level in self.levels.iter().rev() {
			let Some(idx) = level.blocks.iter().position(|(block_hash, _)| block_hash == next_hash)
			else {
				// The overlay chain cannot be interrupted.
				if !overlays.is_empty() {
					return Err(StateDbError::InvalidBlock)
				}
				continue;
			};

			overlays.push(level.blocks[idx].1.clone());

			let Some(parent_hash) = self.parents.get(next_hash) else {
				return Err(StateDbError::InvalidBlock)
			};
			next_hash = parent_hash;
		}

		// The overlay chain can be empty only if the block that we are looking
		// for is the last finalized one, but that has been already checked.
		if overlays.is_empty() {
			return Err(StateDbError::InvalidBlock)
		}

		Ok(overlays)
	}
}
