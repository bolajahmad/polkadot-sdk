use super::{Error, Hash, IsPruned, LastCanonicalized, NomtOverlay, PruningMode, StateDbError};
use parking_lot::{Condvar, Mutex, RwLock};
use sp_database::NomtChanges;
use std::{
	collections::VecDeque,
	sync::{Arc, Weak},
};

pub struct StateDb<BlockHash: Hash> {
	pub(super) mode: PruningMode,
	overlays: VecDeque<(u64, BlockHash, Arc<NomtOverlay>)>,
	last_canonicalized: Option<(u64, BlockHash)>,
	canonicalization_sync_data: Option<Arc<(Mutex<bool>, Condvar)>>,
	_phantom: core::marker::PhantomData<BlockHash>,
}

impl<BlockHash: Hash> StateDb<BlockHash> {
	pub(super) fn new(mode: PruningMode) -> Self {
		Self {
			overlays: VecDeque::new(),
			mode,
			last_canonicalized: None,
			canonicalization_sync_data: None,
			_phantom: core::marker::PhantomData::default(),
		}
	}

	pub(super) fn insert_block(
		&mut self,
		hash: &BlockHash,
		number: u64,
		parent_hash: &BlockHash,
		overlay: NomtOverlay,
	) -> Result<(), StateDbError> {
		// TODO: handle case where number > 0 but overlays is empty,
		// number - 1 should be assumed to be the last canonicalized.
		if let Some((last_number, last_hash, _last_overlay)) = self.overlays.back() {
			if last_number + 1 != number {
				return Err(StateDbError::InvalidBlockNumber)
			}

			if last_hash != parent_hash {
				return Err(StateDbError::InvalidParent)
			}
		}
		self.overlays.push_back((number, hash.clone(), Arc::new(overlay)));
		Ok(())
	}

	pub(super) fn canonicalize_block(
		&mut self,
		hash: &BlockHash,
	) -> Result<NomtChanges, StateDbError> {
		match self.overlays.front() {
			Some((_, front_hash, _)) if front_hash == hash => (),
			_ => return Err(StateDbError::InvalidBlock),
		}

		// UNWRAP: overlays has been checked above to not be empty.
		let (canonicalized_number, canonicalized_hash, canonicalized_overlay) =
			self.overlays.pop_front().unwrap();

		self.wait_for_canonicalization();
		let sync_data = Arc::new((Mutex::new(false), Condvar::new()));
		self.last_canonicalized = Some((canonicalized_number, canonicalized_hash));
		self.canonicalization_sync_data = Some(sync_data.clone());

		Ok(NomtChanges { overlay: canonicalized_overlay, sync_data })
	}

	pub(super) fn last_canonicalized(&self) -> LastCanonicalized {
		self.last_canonicalized
			.as_ref()
			.map(|&(n, _)| LastCanonicalized::Block(n))
			.unwrap_or(LastCanonicalized::None)
	}

	pub(super) fn wait_for_canonicalization(&self) {
		if let Some(sync_data) = self.canonicalization_sync_data.as_ref() {
			let (ref lock, ref cvar) = &**sync_data;
			let mut done = lock.lock();
			if !*done {
				cvar.wait(&mut done);
			}
		}
	}

	pub(super) fn is_pruned(&self, hash: &BlockHash, number: u64) -> IsPruned {
		self.wait_for_canonicalization();

		let Some((last_canonicalized_number, last_canonicalized_hash)) =
			self.last_canonicalized.as_ref()
		else {
			return IsPruned::NotPruned
		};

		if number < *last_canonicalized_number {
			IsPruned::Pruned
		} else if (&number == last_canonicalized_number && hash == last_canonicalized_hash) ||
			self.overlays.iter().any(|(_, block_hash, _)| block_hash == hash)
		{
			IsPruned::NotPruned
		} else {
			todo!()
		}
	}

	pub fn overlays(&self, hash: &BlockHash) -> Vec<Arc<NomtOverlay>> {
		self.wait_for_canonicalization();

		let Some(idx) = self.overlays.iter().position(|(_, block_hash, _)| block_hash == hash)
		else {
			return vec![]
		};

		self.overlays
			.range(0..=idx)
			.map(|(_, _, overlay)| overlay.clone())
			.rev()
			.collect()
	}
}
