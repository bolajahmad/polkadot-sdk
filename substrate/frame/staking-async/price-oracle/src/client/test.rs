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

//! Tests for pallet-price-oracle-client

use crate::client::{mock::*, ValidatorSet, ValidatorSetStorage};
use frame_support::assert_ok;
use pallet_session::{SessionManager, ShouldEndSession};

#[test]
fn receives_validator_set_and_activates() {
	new_test_ext().execute_with(|| {
		// when
		assert_eq!(ValidatorSetStorage::<T>::get(), ValidatorSet::None);

		// then won't trigger session change.
		assert!(!PriceOracleClient::should_end_session(42));

		// when a validator set comes from RC
		assert_ok!(PriceOracleClient::relay_new_validator_set(
			RuntimeOrigin::root(),
			vec![1, 2, 3]
		));

		// then storage is set
		assert_eq!(ValidatorSetStorage::<T>::get(), ValidatorSet::ToPlan(vec![1, 2, 3]));
		// then we will ask session to end the session
		assert!(PriceOracleClient::should_end_session(42));

		// when session will call our `new_session` (among other calls), in which we return the
		// validator set to be activated
		assert_eq!(PriceOracleClient::new_session(1), Some(vec![1, 2, 3]));
		// then we have changed our inner storage to `Planned`
		assert_eq!(ValidatorSetStorage::<T>::get(), ValidatorSet::Planned);
		// then we are still telling session to rotate session one more time.
		assert!(PriceOracleClient::should_end_session(42));

		// when session will call our `new_session` (among other calls), in which we return `None`
		assert_eq!(PriceOracleClient::new_session(2), None);
		// then we have changed our inner storage to `None`
		assert_eq!(ValidatorSetStorage::<T>::get(), ValidatorSet::None);
		// then we are not telling session to rotate session one more time.
		assert!(!PriceOracleClient::should_end_session(42));
	})
}
