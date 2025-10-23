use super::{
	choose_pruning_mode, fetch_stored_pruning_mode,
	noncanonical::NonCanonicalOverlay,
	pruning::{HaveBlock, RefWindow},
	Constraints, DBValue, Error, Hash, IsPruned, LastCanonicalized, PinError, PruningMode,
	StateDbError, LOG_TARGET, LOG_TARGET_PIN, PRUNING_MODE, PRUNING_MODE_ARCHIVE,
	PRUNING_MODE_ARCHIVE_CANON, PRUNING_MODE_CONSTRAINED,
};

use codec::Codec;
use log::trace;
use std::{
	collections::{hash_map::Entry, HashMap},
	fmt,
};

/// Backend database trait. Read-only.
pub trait MetaDb {
	type Error: fmt::Debug;

	/// Get meta value, such as the journal.
	fn get_meta(&self, key: &[u8]) -> Result<Option<DBValue>, Self::Error>;
}

/// Backend database trait. Read-only.
pub trait NodeDb {
	type Key: ?Sized;
	type Error: fmt::Debug;

	/// Get state trie node.
	fn get(&self, key: &Self::Key) -> Result<Option<DBValue>, Self::Error>;
}

/// A set of state node changes.
#[derive(Default, Debug, Clone)]
pub struct ChangeSet<H: Hash> {
	/// Inserted nodes.
	pub inserted: Vec<(H, DBValue)>,
	/// Deleted nodes.
	pub deleted: Vec<H>,
}

/// A set of changes to the backing database.
#[derive(Default, Debug, Clone)]
pub struct CommitSet<H: Hash> {
	/// State node changes.
	pub data: ChangeSet<H>,
	/// Metadata changes.
	pub meta: ChangeSet<Vec<u8>>,
}

pub(super) fn to_meta_key<S: Codec>(suffix: &[u8], data: &S) -> Vec<u8> {
	let mut buffer = data.encode();
	buffer.extend(suffix);
	buffer
}

/// State DB maintenance. See module description.
/// Can be shared across threads.
pub struct StateDb<BlockHash: Hash, Key: Hash, D: MetaDb> {
	pub mode: PruningMode,
	pub non_canonical: NonCanonicalOverlay<BlockHash, Key>,
	pub pruning: Option<RefWindow<BlockHash, Key, D>>,
	pub pinned: HashMap<BlockHash, u32>,
	pub ref_counting: bool,
}

impl<BlockHash: Hash, Key: Hash, D: MetaDb> StateDb<BlockHash, Key, D> {
	pub fn new(
		mode: PruningMode,
		ref_counting: bool,
		db: D,
	) -> Result<StateDb<BlockHash, Key, D>, Error<D::Error>> {
		trace!(target: LOG_TARGET, "StateDb settings: {:?}. Ref-counting: {}", mode, ref_counting);

		let non_canonical: NonCanonicalOverlay<BlockHash, Key> = NonCanonicalOverlay::new(&db)?;
		let pruning: Option<RefWindow<BlockHash, Key, D>> = match mode {
			PruningMode::Constrained(Constraints { max_blocks }) =>
				Some(RefWindow::new(db, max_blocks.unwrap_or(0), ref_counting)?),
			PruningMode::ArchiveAll | PruningMode::ArchiveCanonical => None,
		};

		Ok(StateDb { mode, non_canonical, pruning, pinned: Default::default(), ref_counting })
	}

	pub fn insert_block(
		&mut self,
		hash: &BlockHash,
		number: u64,
		parent_hash: &BlockHash,
		mut changeset: ChangeSet<Key>,
	) -> Result<CommitSet<Key>, Error<D::Error>> {
		match self.mode {
			PruningMode::ArchiveAll => {
				changeset.deleted.clear();
				// write changes immediately
				Ok(CommitSet { data: changeset, meta: Default::default() })
			},
			PruningMode::Constrained(_) | PruningMode::ArchiveCanonical => self
				.non_canonical
				.insert(hash, number, parent_hash, changeset)
				.map_err(Into::into),
		}
	}

	pub fn canonicalize_block(
		&mut self,
		hash: &BlockHash,
	) -> Result<CommitSet<Key>, Error<D::Error>> {
		// NOTE: it is important that the change to `LAST_CANONICAL` (emit from
		// `non_canonical.canonicalize`) and the insert of the new pruning journal (emit from
		// `pruning.note_canonical`) are collected into the same `CommitSet` and are committed to
		// the database atomically to keep their consistency when restarting the node
		let mut commit = CommitSet::default();
		if self.mode == PruningMode::ArchiveAll {
			return Ok(commit)
		}
		let number = self.non_canonical.canonicalize(hash, &mut commit)?;
		if self.mode == PruningMode::ArchiveCanonical {
			commit.data.deleted.clear();
		}
		if let Some(ref mut pruning) = self.pruning {
			pruning.note_canonical(hash, number, &mut commit)?;
		}
		self.prune(&mut commit)?;
		Ok(commit)
	}

	/// Returns the block number of the last canonicalized block.
	pub fn last_canonicalized(&self) -> LastCanonicalized {
		if self.mode == PruningMode::ArchiveAll {
			LastCanonicalized::NotCanonicalizing
		} else {
			self.non_canonical
				.last_canonicalized_block_number()
				.map(LastCanonicalized::Block)
				.unwrap_or_else(|| LastCanonicalized::None)
		}
	}

	pub fn is_pruned(&self, hash: &BlockHash, number: u64) -> IsPruned {
		match self.mode {
			PruningMode::ArchiveAll => IsPruned::NotPruned,
			PruningMode::ArchiveCanonical | PruningMode::Constrained(_) => {
				if self
					.non_canonical
					.last_canonicalized_block_number()
					.map(|c| number > c)
					.unwrap_or(true)
				{
					if self.non_canonical.have_block(hash) {
						IsPruned::NotPruned
					} else {
						IsPruned::Pruned
					}
				} else {
					match self.pruning.as_ref() {
						// We don't know for sure.
						None => IsPruned::MaybePruned,
						Some(pruning) => match pruning.have_block(hash, number) {
							HaveBlock::No => IsPruned::Pruned,
							HaveBlock::Yes => IsPruned::NotPruned,
							HaveBlock::Maybe => IsPruned::MaybePruned,
						},
					}
				}
			},
		}
	}

	pub fn prune(&mut self, commit: &mut CommitSet<Key>) -> Result<(), Error<D::Error>> {
		if let (&mut Some(ref mut pruning), PruningMode::Constrained(constraints)) =
			(&mut self.pruning, &self.mode)
		{
			loop {
				if pruning.window_size() <= constraints.max_blocks.unwrap_or(0) as u64 {
					break
				}

				let pinned = &self.pinned;
				match pruning.next_hash() {
					// the block record is temporary unavailable, break and try next time
					Err(Error::StateDb(StateDbError::BlockUnavailable)) => break,
					res =>
						if res?.map_or(false, |h| pinned.contains_key(&h)) {
							break
						},
				}
				match pruning.prune_one(commit) {
					// this branch should not reach as previous `next_hash` don't return error
					// keeping it for robustness
					Err(Error::StateDb(StateDbError::BlockUnavailable)) => break,
					res => res?,
				}
			}
		}
		Ok(())
	}

	/// Revert all non-canonical blocks with the best block number.
	/// Returns a database commit or `None` if not possible.
	/// For archive an empty commit set is returned.
	pub fn revert_one(&mut self) -> Option<CommitSet<Key>> {
		match self.mode {
			PruningMode::ArchiveAll => Some(CommitSet::default()),
			PruningMode::ArchiveCanonical | PruningMode::Constrained(_) =>
				self.non_canonical.revert_one(),
		}
	}

	pub fn remove(&mut self, hash: &BlockHash) -> Option<CommitSet<Key>> {
		match self.mode {
			PruningMode::ArchiveAll => Some(CommitSet::default()),
			PruningMode::ArchiveCanonical | PruningMode::Constrained(_) =>
				self.non_canonical.remove(hash),
		}
	}

	pub fn pin<F>(&mut self, hash: &BlockHash, number: u64, hint: F) -> Result<(), PinError>
	where
		F: Fn() -> bool,
	{
		match self.mode {
			PruningMode::ArchiveAll => Ok(()),
			PruningMode::ArchiveCanonical | PruningMode::Constrained(_) => {
				let have_block = self.non_canonical.have_block(hash) ||
					self.pruning.as_ref().map_or_else(
						|| hint(),
						|pruning| match pruning.have_block(hash, number) {
							HaveBlock::No => false,
							HaveBlock::Yes => true,
							HaveBlock::Maybe => hint(),
						},
					);
				if have_block {
					let refs = self.pinned.entry(hash.clone()).or_default();
					if *refs == 0 {
						trace!(target: LOG_TARGET_PIN, "Pinned block: {:?}", hash);
						self.non_canonical.pin(hash);
					}
					*refs += 1;
					Ok(())
				} else {
					Err(PinError::InvalidBlock)
				}
			},
		}
	}

	pub fn unpin(&mut self, hash: &BlockHash) {
		match self.pinned.entry(hash.clone()) {
			Entry::Occupied(mut entry) => {
				*entry.get_mut() -= 1;
				if *entry.get() == 0 {
					trace!(target: LOG_TARGET_PIN, "Unpinned block: {:?}", hash);
					entry.remove();
					self.non_canonical.unpin(hash);
				} else {
					trace!(target: LOG_TARGET_PIN, "Releasing reference for {:?}", hash);
				}
			},
			Entry::Vacant(_) => {},
		}
	}

	pub fn sync(&mut self) {
		self.non_canonical.sync();
	}

	pub fn get<DB: NodeDb, Q: ?Sized>(
		&self,
		key: &Q,
		db: &DB,
	) -> Result<Option<DBValue>, Error<DB::Error>>
	where
		Q: AsRef<DB::Key>,
		Key: std::borrow::Borrow<Q>,
		Q: std::hash::Hash + Eq,
	{
		if let Some(value) = self.non_canonical.get(key) {
			return Ok(Some(value))
		}
		db.get(key.as_ref()).map_err(Error::Db)
	}
}
