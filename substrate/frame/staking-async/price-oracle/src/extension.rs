// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! # Transaction Extensions for the Price Oracle Parachain
//!
//! This module provides specialized [`TransactionExtension`]s for the price-oracle runtime. These
//! extensions are essential for spam prevention and transaction prioritization in a runtime that
//! intentionally lacks standard pallets like `balances` and `transaction-payment`.
//!
//! ## Extensions
//!
//! ### [`OnlyOracleAuthorities`]
//!
//! This extension blocks ALL incoming signed transactions unless:
//! 1. The origin is root
//! 2. The signer is a registered oracle authority (in [`crate::oracle::Authorities`])
//! 3. The signer is in the `ExtraSigners` list (e.g., sudo key holders)
//!
//! This is the **primary spam prevention mechanism** for the price-oracle parachain. Without
//! balance requirements or transaction fees, this extension ensures only authorized parties can
//! submit transactions.
//!
//! ### [`SetPriorityFromProducedIn`]
//!
//! This extension extracts the `produced_in` field from [`crate::oracle::Call::vote`] calls and
//! sets it as the transaction priority. This ensures that more recent votes are prioritized over
//! older ones in the transaction pool.
//!
//! ## Usage
//!
//! Both extensions should be included in the runtime's `TxExtension` tuple:
//!
//! ```ignore
//! pub type TxExtension = (
//!     // ... other extensions ...
//!     OnlyOracleAuthorities<Runtime, ExtraSignersProvider>,
//!     SetPriorityFromProducedIn<Runtime>,
//! );
//! ```
//!
//! [`TransactionExtension`]: sp_runtime::traits::TransactionExtension

extern crate alloc;

use super::oracle::Call as OracleCall;
use codec::{Decode, DecodeWithMemTracking, Encode};
use frame_support::{
	dispatch::DispatchInfo,
	pallet_prelude::{InvalidTransaction, TransactionSource},
	traits::{CallerTrait, Get, IsSubType, OriginTrait},
	weights::Weight,
};
use scale_info::TypeInfo;
use sp_runtime::{
	traits::{
		AsSystemOriginSigner, DispatchInfoOf, Dispatchable, PostDispatchInfoOf,
		TransactionExtension, ValidateResult,
	},
	transaction_validity::{TransactionPriority, TransactionValidityError, ValidTransaction},
	DispatchResult, SaturatedConversion,
};

/// Transaction extension that extracts the `produced_in` field from the call body
/// and sets it as the transaction priority.
#[derive(Encode, Decode, DecodeWithMemTracking, Clone, Eq, PartialEq, TypeInfo)]
#[scale_info(skip_type_params(T))]
pub struct SetPriorityFromProducedIn<T: super::oracle::Config>(core::marker::PhantomData<T>);

impl<T: super::oracle::Config> Default for SetPriorityFromProducedIn<T> {
	fn default() -> Self {
		Self(core::marker::PhantomData)
	}
}

impl<T: super::oracle::Config> core::fmt::Debug for SetPriorityFromProducedIn<T> {
	fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
		write!(f, "SetPriorityFromProducedIn")
	}
}

impl<T> TransactionExtension<<T as frame_system::Config>::RuntimeCall>
	for SetPriorityFromProducedIn<T>
where
	T: super::oracle::Config + frame_system::Config + Send + Sync,
	<T as frame_system::Config>::RuntimeCall: Dispatchable<Info = DispatchInfo>,
	<<T as frame_system::Config>::RuntimeCall as Dispatchable>::RuntimeOrigin:
		AsSystemOriginSigner<T::AccountId> + Clone,
	<T as frame_system::Config>::RuntimeCall: IsSubType<OracleCall<T>>,
{
	const IDENTIFIER: &'static str = "SetPriorityFromProducedIn";
	type Implicit = ();
	type Val = ();
	type Pre = ();

	fn weight(&self, _call: &<T as frame_system::Config>::RuntimeCall) -> Weight {
		// Minimal weight as this is just reading from the call
		Weight::from_parts(1_000, 0)
	}

	fn validate(
		&self,
		origin: <T as frame_system::Config>::RuntimeOrigin,
		call: &<T as frame_system::Config>::RuntimeCall,
		_info: &DispatchInfoOf<<T as frame_system::Config>::RuntimeCall>,
		_len: usize,
		_self_implicit: Self::Implicit,
		_inherited_implication: &impl Encode,
		_source: TransactionSource,
	) -> ValidateResult<Self::Val, <T as frame_system::Config>::RuntimeCall> {
		let mut priority: TransactionPriority = 0;

		// Check if our call `IsSubType` of the `RuntimeCall`
		if let Some(OracleCall::vote { produced_in, .. }) = call.is_sub_type() {
			log::debug!(target: "runtime::price-oracle::priority-extension", "Setting priority for vote call");
			priority = (*produced_in).saturated_into();
		}

		let validity = ValidTransaction { priority, ..Default::default() };

		Ok((validity, (), origin))
	}

	fn prepare(
		self,
		_val: Self::Val,
		_origin: &<T as frame_system::Config>::RuntimeOrigin,
		_call: &<T as frame_system::Config>::RuntimeCall,
		_info: &DispatchInfoOf<<T as frame_system::Config>::RuntimeCall>,
		_len: usize,
	) -> Result<Self::Pre, TransactionValidityError> {
		Ok(())
	}

	fn post_dispatch_details(
		_pre: Self::Pre,
		_info: &DispatchInfo,
		_post_info: &PostDispatchInfoOf<<T as frame_system::Config>::RuntimeCall>,
		_len: usize,
		_result: &DispatchResult,
	) -> Result<Weight, TransactionValidityError> {
		Ok(Default::default())
	}
}

/// Transaction extension that will block any incoming transactions from any signed account, to any
/// call in the runtime, except for oracle authorities and extra allowed signers.
///
/// `ExtraSigners` is a `Get` type that returns a list of additional account IDs that are allowed
/// to submit transactions. This can be used to allow sudo key holders or other privileged accounts.
#[derive(Encode, Decode, DecodeWithMemTracking, Clone, Eq, PartialEq, TypeInfo)]
#[scale_info(skip_type_params(T, ExtraSigners))]
pub struct OnlyOracleAuthorities<T, ExtraSigners = ()>(
	core::marker::PhantomData<(T, ExtraSigners)>,
);

impl<T, ExtraSigners> Default for OnlyOracleAuthorities<T, ExtraSigners> {
	fn default() -> Self {
		Self(core::marker::PhantomData)
	}
}

impl<T, ExtraSigners> core::fmt::Debug for OnlyOracleAuthorities<T, ExtraSigners> {
	fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
		write!(f, "OnlyOracleAuthorities")
	}
}

impl<T, ExtraSigners> TransactionExtension<<T as frame_system::Config>::RuntimeCall>
	for OnlyOracleAuthorities<T, ExtraSigners>
where
	T: super::oracle::Config + frame_system::Config + Send + Sync,
	<T as frame_system::Config>::RuntimeCall: Dispatchable<Info = DispatchInfo>,
	<<T as frame_system::Config>::RuntimeCall as Dispatchable>::RuntimeOrigin:
		AsSystemOriginSigner<T::AccountId> + Clone,
	<T as frame_system::Config>::RuntimeCall: IsSubType<OracleCall<T>>,
	ExtraSigners: Get<alloc::vec::Vec<T::AccountId>> + Clone + Eq + Send + Sync + 'static,
{
	const IDENTIFIER: &'static str = "OnlyOracleAuthorities";
	type Implicit = ();
	type Val = ();
	type Pre = ();

	fn weight(&self, _call: &<T as frame_system::Config>::RuntimeCall) -> Weight {
		// 1 storage read for authorities, ExtraSigners::get() may add more
		T::DbWeight::get().reads(1)
	}

	fn validate(
		&self,
		origin: <T as frame_system::Config>::RuntimeOrigin,
		_call: &<T as frame_system::Config>::RuntimeCall,
		_info: &DispatchInfoOf<<T as frame_system::Config>::RuntimeCall>,
		_len: usize,
		_self_implicit: Self::Implicit,
		_inherited_implication: &impl Encode,
		_source: TransactionSource,
	) -> ValidateResult<Self::Val, <T as frame_system::Config>::RuntimeCall> {
		let caller = origin.caller();
		match (caller.is_root(), caller.as_signed()) {
			(true, _) => {
				log::debug!(target: "runtime::price-oracle::only-oracle-authorities", "Allowing root origin");
				return Ok((ValidTransaction::default(), (), origin));
			},
			(false, Some(signer))
				if crate::oracle::Authorities::<T>::get().contains_key(signer) =>
			{
				log::debug!(target: "runtime::price-oracle::only-oracle-authorities", "Allowing oracle authority");
				return Ok((ValidTransaction::default(), (), origin));
			},
			(false, Some(signer)) if ExtraSigners::get().contains(signer) => {
				log::debug!(target: "runtime::price-oracle::only-oracle-authorities", "Allowing extra signer");
				return Ok((ValidTransaction::default(), (), origin));
			},
			_ => return Err(TransactionValidityError::Invalid(InvalidTransaction::BadSigner)),
		}
	}

	fn prepare(
		self,
		_val: Self::Val,
		_origin: &sp_runtime::traits::DispatchOriginOf<<T as frame_system::Config>::RuntimeCall>,
		_call: &<T as frame_system::Config>::RuntimeCall,
		_info: &DispatchInfoOf<<T as frame_system::Config>::RuntimeCall>,
		_len: usize,
	) -> Result<Self::Pre, TransactionValidityError> {
		Ok(())
	}

	fn post_dispatch_details(
		_pre: Self::Pre,
		_info: &DispatchInfoOf<<T as frame_system::Config>::RuntimeCall>,
		_post_info: &PostDispatchInfoOf<<T as frame_system::Config>::RuntimeCall>,
		_len: usize,
		_result: &DispatchResult,
	) -> Result<Weight, TransactionValidityError> {
		Ok(Default::default())
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::oracle::mock::{ExtBuilder, Runtime, RuntimeCall, RuntimeOrigin};
	use frame_support::dispatch::GetDispatchInfo;
	use sp_runtime::{
		traits::{TransactionExtension, TxBaseImplication},
		FixedU128,
	};

	fn vote_call(produced_in: u64) -> RuntimeCall {
		RuntimeCall::PriceOracle(crate::oracle::Call::vote {
			asset_id: 1,
			price: FixedU128::from_u32(100),
			produced_in,
		})
	}

	fn non_oracle_call() -> RuntimeCall {
		RuntimeCall::System(frame_system::Call::remark { remark: vec![] })
	}

	mod set_priority_from_produced_in {
		use super::*;

		fn validate_priority(call: &RuntimeCall) -> TransactionPriority {
			let ext = SetPriorityFromProducedIn::<Runtime>::default();
			let info = call.get_dispatch_info();
			ext.validate(
				RuntimeOrigin::signed(1),
				call,
				&info,
				0,
				(),
				&TxBaseImplication(()),
				TransactionSource::External,
			)
			.unwrap()
			.0
			.priority
		}

		#[test]
		fn sets_priority_for_vote_call() {
			ExtBuilder::default().build_and_execute(|| {
				assert_eq!(validate_priority(&vote_call(42)), 42);
			});
		}

		#[test]
		fn noop_for_non_oracle_call() {
			ExtBuilder::default().build_and_execute(|| {
				assert_eq!(validate_priority(&non_oracle_call()), 0);
			});
		}
	}

	mod only_oracle_authorities {
		use super::*;
		use core::cell::RefCell;

		std::thread_local! {
			static EXTRA_SIGNERS: RefCell<Vec<u64>> = RefCell::new(vec![]);
		}

		#[derive(Clone, Eq, PartialEq)]
		pub struct MockExtraSigners;
		impl Get<Vec<u64>> for MockExtraSigners {
			fn get() -> Vec<u64> {
				EXTRA_SIGNERS.with(|s| s.borrow().clone())
			}
		}

		fn set_extra_signers(signers: Vec<u64>) {
			EXTRA_SIGNERS.with(|s| *s.borrow_mut() = signers);
		}

		type TestExtension = OnlyOracleAuthorities<Runtime, MockExtraSigners>;

		fn validate_with(
			origin: RuntimeOrigin,
			call: &RuntimeCall,
		) -> ValidateResult<(), RuntimeCall> {
			let ext = TestExtension::default();
			let info = call.get_dispatch_info();
			ext.validate(
				origin,
				call,
				&info,
				0,
				(),
				&TxBaseImplication(()),
				TransactionSource::External,
			)
		}

		#[test]
		fn allows_authority_for_any_call() {
			ExtBuilder::default().build_and_execute(|| {
				let authority = RuntimeOrigin::signed(1);
				assert!(validate_with(authority.clone(), &vote_call(7)).is_ok());
				assert!(validate_with(authority, &non_oracle_call()).is_ok());
			});
		}

		#[test]
		fn rejects_non_authority() {
			ExtBuilder::default().build_and_execute(|| {
				assert!(matches!(
					validate_with(RuntimeOrigin::signed(99), &vote_call(7)),
					Err(TransactionValidityError::Invalid(InvalidTransaction::BadSigner))
				));
			});
		}

		#[test]
		fn allows_root() {
			ExtBuilder::default().build_and_execute(|| {
				assert!(validate_with(RuntimeOrigin::root(), &vote_call(7)).is_ok());
				assert!(validate_with(RuntimeOrigin::root(), &non_oracle_call()).is_ok());
			});
		}

		#[test]
		fn allows_extra_signers() {
			ExtBuilder::default().build_and_execute(|| {
				set_extra_signers(vec![42]);
				assert!(validate_with(RuntimeOrigin::signed(42), &vote_call(7)).is_ok());
				assert!(validate_with(RuntimeOrigin::signed(42), &non_oracle_call()).is_ok());
				// Non-extra signer still rejected
				assert!(matches!(
					validate_with(RuntimeOrigin::signed(99), &vote_call(7)),
					Err(TransactionValidityError::Invalid(InvalidTransaction::BadSigner))
				));
			});
		}
	}
}
