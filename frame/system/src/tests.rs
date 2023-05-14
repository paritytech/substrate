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

use crate::*;
use frame_support::{
	assert_noop, assert_ok,
	dispatch::{Pays, PostDispatchInfo, WithPostDispatchInfo},
};
use mock::{RuntimeOrigin, *};
use sp_core::H256;
use sp_runtime::{
	traits::{BlakeTwo256, Header},
	DispatchError, DispatchErrorWithPostInfo,
};

#[test]
fn origin_works() {
	let o = RuntimeOrigin::from(RawOrigin::<u64>::Signed(1u64));
	let x: Result<RawOrigin<u64>, RuntimeOrigin> = o.into();
	assert_eq!(x.unwrap(), RawOrigin::<u64>::Signed(1u64));
}

#[test]
fn stored_map_works() {
	new_test_ext().execute_with(|| {
		assert_eq!(System::inc_providers(&0), IncRefStatus::Created);
		assert_ok!(System::insert(&0, 42));
		assert!(!System::is_provider_required(&0));

		assert_eq!(
			Account::<Test>::get(0),
			AccountInfo { nonce: 0, providers: 1, consumers: 0, sufficients: 0, data: 42 }
		);

		assert_ok!(System::inc_consumers(&0));
		assert!(System::is_provider_required(&0));

		assert_ok!(System::insert(&0, 69));
		assert!(System::is_provider_required(&0));

		System::dec_consumers(&0);
		assert!(!System::is_provider_required(&0));

		assert!(Killed::get().is_empty());
		assert_ok!(System::remove(&0));
		assert_ok!(System::dec_providers(&0));
		assert_eq!(Killed::get(), vec![0u64]);
	});
}

#[test]
fn provider_ref_handover_to_self_sufficient_ref_works() {
	new_test_ext().execute_with(|| {
		assert_eq!(System::inc_providers(&0), IncRefStatus::Created);
		System::inc_account_nonce(&0);
		assert_eq!(System::account_nonce(&0), 1);

		// a second reference coming and going doesn't change anything.
		assert_eq!(System::inc_sufficients(&0), IncRefStatus::Existed);
		assert_eq!(System::dec_sufficients(&0), DecRefStatus::Exists);
		assert_eq!(System::account_nonce(&0), 1);

		// a provider reference coming and going doesn't change anything.
		assert_eq!(System::inc_providers(&0), IncRefStatus::Existed);
		assert_eq!(System::dec_providers(&0).unwrap(), DecRefStatus::Exists);
		assert_eq!(System::account_nonce(&0), 1);

		// decreasing the providers with a self-sufficient present should not delete the account
		assert_eq!(System::inc_sufficients(&0), IncRefStatus::Existed);
		assert_eq!(System::dec_providers(&0).unwrap(), DecRefStatus::Exists);
		assert_eq!(System::account_nonce(&0), 1);

		// decreasing the sufficients should delete the account
		assert_eq!(System::dec_sufficients(&0), DecRefStatus::Reaped);
		assert_eq!(System::account_nonce(&0), 0);
	});
}

#[test]
fn self_sufficient_ref_handover_to_provider_ref_works() {
	new_test_ext().execute_with(|| {
		assert_eq!(System::inc_sufficients(&0), IncRefStatus::Created);
		System::inc_account_nonce(&0);
		assert_eq!(System::account_nonce(&0), 1);

		// a second reference coming and going doesn't change anything.
		assert_eq!(System::inc_providers(&0), IncRefStatus::Existed);
		assert_eq!(System::dec_providers(&0).unwrap(), DecRefStatus::Exists);
		assert_eq!(System::account_nonce(&0), 1);

		// a sufficient reference coming and going doesn't change anything.
		assert_eq!(System::inc_sufficients(&0), IncRefStatus::Existed);
		assert_eq!(System::dec_sufficients(&0), DecRefStatus::Exists);
		assert_eq!(System::account_nonce(&0), 1);

		// decreasing the sufficients with a provider present should not delete the account
		assert_eq!(System::inc_providers(&0), IncRefStatus::Existed);
		assert_eq!(System::dec_sufficients(&0), DecRefStatus::Exists);
		assert_eq!(System::account_nonce(&0), 1);

		// decreasing the providers should delete the account
		assert_eq!(System::dec_providers(&0).unwrap(), DecRefStatus::Reaped);
		assert_eq!(System::account_nonce(&0), 0);
	});
}

#[test]
fn sufficient_cannot_support_consumer() {
	new_test_ext().execute_with(|| {
		assert_eq!(System::inc_sufficients(&0), IncRefStatus::Created);
		System::inc_account_nonce(&0);
		assert_eq!(System::account_nonce(&0), 1);
		assert_noop!(System::inc_consumers(&0), DispatchError::NoProviders);

		assert_eq!(System::inc_providers(&0), IncRefStatus::Existed);
		assert_ok!(System::inc_consumers(&0));
		assert_noop!(System::dec_providers(&0), DispatchError::ConsumerRemaining);
	});
}

#[test]
fn provider_required_to_support_consumer() {
	new_test_ext().execute_with(|| {
		assert_noop!(System::inc_consumers(&0), DispatchError::NoProviders);

		assert_eq!(System::inc_providers(&0), IncRefStatus::Created);
		System::inc_account_nonce(&0);
		assert_eq!(System::account_nonce(&0), 1);

		assert_eq!(System::inc_providers(&0), IncRefStatus::Existed);
		assert_eq!(System::dec_providers(&0).unwrap(), DecRefStatus::Exists);
		assert_eq!(System::account_nonce(&0), 1);

		assert_ok!(System::inc_consumers(&0));
		assert_noop!(System::dec_providers(&0), DispatchError::ConsumerRemaining);

		System::dec_consumers(&0);
		assert_eq!(System::dec_providers(&0).unwrap(), DecRefStatus::Reaped);
		assert_eq!(System::account_nonce(&0), 0);
	});
}

#[test]
fn deposit_event_should_work() {
	new_test_ext().execute_with(|| {
		System::reset_events();
		System::initialize(&1, &[0u8; 32].into(), &Default::default());
		System::note_finished_extrinsics();
		System::deposit_event(SysEvent::CodeUpdated);
		System::finalize();
		assert_eq!(
			System::events(),
			vec![EventRecord {
				phase: Phase::Finalization,
				event: SysEvent::CodeUpdated.into(),
				topics: vec![],
			}]
		);

		let normal_base = <Test as crate::Config>::BlockWeights::get()
			.get(DispatchClass::Normal)
			.base_extrinsic;

		System::reset_events();
		System::initialize(&2, &[0u8; 32].into(), &Default::default());
		System::deposit_event(SysEvent::NewAccount { account: 32 });
		System::note_finished_initialize();
		System::deposit_event(SysEvent::KilledAccount { account: 42 });
		System::note_applied_extrinsic(&Ok(().into()), Default::default());
		System::note_applied_extrinsic(&Err(DispatchError::BadOrigin.into()), Default::default());
		System::note_finished_extrinsics();
		System::deposit_event(SysEvent::NewAccount { account: 3 });
		System::finalize();
		assert_eq!(
			System::events(),
			vec![
				EventRecord {
					phase: Phase::Initialization,
					event: SysEvent::NewAccount { account: 32 }.into(),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::ApplyExtrinsic(0),
					event: SysEvent::KilledAccount { account: 42 }.into(),
					topics: vec![]
				},
				EventRecord {
					phase: Phase::ApplyExtrinsic(0),
					event: SysEvent::ExtrinsicSuccess {
						dispatch_info: DispatchInfo { weight: normal_base, ..Default::default() }
					}
					.into(),
					topics: vec![]
				},
				EventRecord {
					phase: Phase::ApplyExtrinsic(1),
					event: SysEvent::ExtrinsicFailed {
						dispatch_error: DispatchError::BadOrigin.into(),
						dispatch_info: DispatchInfo { weight: normal_base, ..Default::default() }
					}
					.into(),
					topics: vec![]
				},
				EventRecord {
					phase: Phase::Finalization,
					event: SysEvent::NewAccount { account: 3 }.into(),
					topics: vec![]
				},
			]
		);
	});
}

#[test]
fn deposit_event_uses_actual_weight_and_pays_fee() {
	new_test_ext().execute_with(|| {
		System::reset_events();
		System::initialize(&1, &[0u8; 32].into(), &Default::default());
		System::note_finished_initialize();

		let normal_base = <Test as crate::Config>::BlockWeights::get()
			.get(DispatchClass::Normal)
			.base_extrinsic;
		let pre_info = DispatchInfo { weight: Weight::from_parts(1000, 0), ..Default::default() };
		System::note_applied_extrinsic(&Ok(from_actual_ref_time(Some(300))), pre_info);
		System::note_applied_extrinsic(&Ok(from_actual_ref_time(Some(1000))), pre_info);
		System::note_applied_extrinsic(
			// values over the pre info should be capped at pre dispatch value
			&Ok(from_actual_ref_time(Some(1200))),
			pre_info,
		);
		System::note_applied_extrinsic(
			&Ok(from_post_weight_info(Some(2_500_000), Pays::Yes)),
			pre_info,
		);
		System::note_applied_extrinsic(&Ok(Pays::No.into()), pre_info);
		System::note_applied_extrinsic(
			&Ok(from_post_weight_info(Some(2_500_000), Pays::No)),
			pre_info,
		);
		System::note_applied_extrinsic(&Ok(from_post_weight_info(Some(500), Pays::No)), pre_info);
		System::note_applied_extrinsic(
			&Err(DispatchError::BadOrigin.with_weight(Weight::from_parts(999, 0))),
			pre_info,
		);

		System::note_applied_extrinsic(
			&Err(DispatchErrorWithPostInfo {
				post_info: PostDispatchInfo { actual_weight: None, pays_fee: Pays::Yes },
				error: DispatchError::BadOrigin,
			}),
			pre_info,
		);
		System::note_applied_extrinsic(
			&Err(DispatchErrorWithPostInfo {
				post_info: PostDispatchInfo {
					actual_weight: Some(Weight::from_parts(800, 0)),
					pays_fee: Pays::Yes,
				},
				error: DispatchError::BadOrigin,
			}),
			pre_info,
		);
		System::note_applied_extrinsic(
			&Err(DispatchErrorWithPostInfo {
				post_info: PostDispatchInfo {
					actual_weight: Some(Weight::from_parts(800, 0)),
					pays_fee: Pays::No,
				},
				error: DispatchError::BadOrigin,
			}),
			pre_info,
		);
		// Also works for operational.
		let operational_base = <Test as crate::Config>::BlockWeights::get()
			.get(DispatchClass::Operational)
			.base_extrinsic;
		assert!(normal_base != operational_base, "Test pre-condition violated");
		let pre_info = DispatchInfo {
			weight: Weight::from_parts(1000, 0),
			class: DispatchClass::Operational,
			..Default::default()
		};
		System::note_applied_extrinsic(&Ok(from_actual_ref_time(Some(300))), pre_info);

		let got = System::events();
		let want = vec![
			EventRecord {
				phase: Phase::ApplyExtrinsic(0),
				event: SysEvent::ExtrinsicSuccess {
					dispatch_info: DispatchInfo {
						weight: Weight::from_parts(300, 0).saturating_add(normal_base),
						..Default::default()
					},
				}
				.into(),
				topics: vec![],
			},
			EventRecord {
				phase: Phase::ApplyExtrinsic(1),
				event: SysEvent::ExtrinsicSuccess {
					dispatch_info: DispatchInfo {
						weight: Weight::from_parts(1000, 0).saturating_add(normal_base),
						..Default::default()
					},
				}
				.into(),
				topics: vec![],
			},
			EventRecord {
				phase: Phase::ApplyExtrinsic(2),
				event: SysEvent::ExtrinsicSuccess {
					dispatch_info: DispatchInfo {
						weight: Weight::from_parts(1000, 0).saturating_add(normal_base),
						..Default::default()
					},
				}
				.into(),
				topics: vec![],
			},
			EventRecord {
				phase: Phase::ApplyExtrinsic(3),
				event: SysEvent::ExtrinsicSuccess {
					dispatch_info: DispatchInfo {
						weight: Weight::from_parts(1000, 0).saturating_add(normal_base),
						pays_fee: Pays::Yes,
						..Default::default()
					},
				}
				.into(),
				topics: vec![],
			},
			EventRecord {
				phase: Phase::ApplyExtrinsic(4),
				event: SysEvent::ExtrinsicSuccess {
					dispatch_info: DispatchInfo {
						weight: Weight::from_parts(1000, 0).saturating_add(normal_base),
						pays_fee: Pays::No,
						..Default::default()
					},
				}
				.into(),
				topics: vec![],
			},
			EventRecord {
				phase: Phase::ApplyExtrinsic(5),
				event: SysEvent::ExtrinsicSuccess {
					dispatch_info: DispatchInfo {
						weight: Weight::from_parts(1000, 0).saturating_add(normal_base),
						pays_fee: Pays::No,
						..Default::default()
					},
				}
				.into(),
				topics: vec![],
			},
			EventRecord {
				phase: Phase::ApplyExtrinsic(6),
				event: SysEvent::ExtrinsicSuccess {
					dispatch_info: DispatchInfo {
						weight: Weight::from_parts(500, 0).saturating_add(normal_base),
						pays_fee: Pays::No,
						..Default::default()
					},
				}
				.into(),
				topics: vec![],
			},
			EventRecord {
				phase: Phase::ApplyExtrinsic(7),
				event: SysEvent::ExtrinsicFailed {
					dispatch_error: DispatchError::BadOrigin.into(),
					dispatch_info: DispatchInfo {
						weight: Weight::from_parts(999, 0).saturating_add(normal_base),
						..Default::default()
					},
				}
				.into(),
				topics: vec![],
			},
			EventRecord {
				phase: Phase::ApplyExtrinsic(8),
				event: SysEvent::ExtrinsicFailed {
					dispatch_error: DispatchError::BadOrigin.into(),
					dispatch_info: DispatchInfo {
						weight: Weight::from_parts(1000, 0).saturating_add(normal_base),
						pays_fee: Pays::Yes,
						..Default::default()
					},
				}
				.into(),
				topics: vec![],
			},
			EventRecord {
				phase: Phase::ApplyExtrinsic(9),
				event: SysEvent::ExtrinsicFailed {
					dispatch_error: DispatchError::BadOrigin.into(),
					dispatch_info: DispatchInfo {
						weight: Weight::from_parts(800, 0).saturating_add(normal_base),
						pays_fee: Pays::Yes,
						..Default::default()
					},
				}
				.into(),
				topics: vec![],
			},
			EventRecord {
				phase: Phase::ApplyExtrinsic(10),
				event: SysEvent::ExtrinsicFailed {
					dispatch_error: DispatchError::BadOrigin.into(),
					dispatch_info: DispatchInfo {
						weight: Weight::from_parts(800, 0).saturating_add(normal_base),
						pays_fee: Pays::No,
						..Default::default()
					},
				}
				.into(),
				topics: vec![],
			},
			EventRecord {
				phase: Phase::ApplyExtrinsic(11),
				event: SysEvent::ExtrinsicSuccess {
					dispatch_info: DispatchInfo {
						weight: Weight::from_parts(300, 0).saturating_add(operational_base),
						class: DispatchClass::Operational,
						..Default::default()
					},
				}
				.into(),
				topics: vec![],
			},
		];
		for (i, event) in want.into_iter().enumerate() {
			assert_eq!(got[i], event, "Event mismatch at index {}", i);
		}
	});
}

#[test]
fn deposit_event_topics() {
	new_test_ext().execute_with(|| {
		const BLOCK_NUMBER: u64 = 1;

		System::reset_events();
		System::initialize(&BLOCK_NUMBER, &[0u8; 32].into(), &Default::default());
		System::note_finished_extrinsics();

		let topics = vec![H256::repeat_byte(1), H256::repeat_byte(2), H256::repeat_byte(3)];

		// We deposit a few events with different sets of topics.
		System::deposit_event_indexed(&topics[0..3], SysEvent::NewAccount { account: 1 }.into());
		System::deposit_event_indexed(&topics[0..1], SysEvent::NewAccount { account: 2 }.into());
		System::deposit_event_indexed(&topics[1..2], SysEvent::NewAccount { account: 3 }.into());

		System::finalize();

		// Check that topics are reflected in the event record.
		assert_eq!(
			System::events(),
			vec![
				EventRecord {
					phase: Phase::Finalization,
					event: SysEvent::NewAccount { account: 1 }.into(),
					topics: topics[0..3].to_vec(),
				},
				EventRecord {
					phase: Phase::Finalization,
					event: SysEvent::NewAccount { account: 2 }.into(),
					topics: topics[0..1].to_vec(),
				},
				EventRecord {
					phase: Phase::Finalization,
					event: SysEvent::NewAccount { account: 3 }.into(),
					topics: topics[1..2].to_vec(),
				}
			]
		);

		// Check that the topic-events mapping reflects the deposited topics.
		// Note that these are indexes of the events.
		assert_eq!(System::event_topics(&topics[0]), vec![(BLOCK_NUMBER, 0), (BLOCK_NUMBER, 1)]);
		assert_eq!(System::event_topics(&topics[1]), vec![(BLOCK_NUMBER, 0), (BLOCK_NUMBER, 2)]);
		assert_eq!(System::event_topics(&topics[2]), vec![(BLOCK_NUMBER, 0)]);
	});
}

#[test]
fn event_util_functions_should_work() {
	new_test_ext().execute_with(|| {
		System::set_block_number(1);
		System::deposit_event(SysEvent::CodeUpdated);

		System::assert_has_event(SysEvent::CodeUpdated.into());
		System::assert_last_event(SysEvent::CodeUpdated.into());
	});
}

#[test]
fn prunes_block_hash_mappings() {
	new_test_ext().execute_with(|| {
		// simulate import of 15 blocks
		for n in 1..=15 {
			System::reset_events();
			System::initialize(&n, &[n as u8 - 1; 32].into(), &Default::default());

			System::finalize();
		}

		// first 5 block hashes are pruned
		for n in 0..5 {
			assert_eq!(System::block_hash(n), H256::zero());
		}

		// the remaining 10 are kept
		for n in 5..15 {
			assert_eq!(System::block_hash(n), [n as u8; 32].into());
		}
	})
}

#[test]
fn set_code_checks_works() {
	struct ReadRuntimeVersion(Vec<u8>);

	impl sp_core::traits::ReadRuntimeVersion for ReadRuntimeVersion {
		fn read_runtime_version(
			&self,
			_wasm_code: &[u8],
			_ext: &mut dyn sp_externalities::Externalities,
		) -> Result<Vec<u8>, String> {
			Ok(self.0.clone())
		}
	}

	let test_data = vec![
		("test", 1, 2, Err(Error::<Test>::SpecVersionNeedsToIncrease)),
		("test", 1, 1, Err(Error::<Test>::SpecVersionNeedsToIncrease)),
		("test2", 1, 1, Err(Error::<Test>::InvalidSpecName)),
		(
			"test",
			2,
			1,
			Ok(Some(<mock::Test as pallet::Config>::BlockWeights::get().max_block).into()),
		),
		("test", 0, 1, Err(Error::<Test>::SpecVersionNeedsToIncrease)),
		("test", 1, 0, Err(Error::<Test>::SpecVersionNeedsToIncrease)),
	];

	for (spec_name, spec_version, impl_version, expected) in test_data.into_iter() {
		let version = RuntimeVersion {
			spec_name: spec_name.into(),
			spec_version,
			impl_version,
			..Default::default()
		};
		let read_runtime_version = ReadRuntimeVersion(version.encode());

		let mut ext = new_test_ext();
		ext.register_extension(sp_core::traits::ReadRuntimeVersionExt::new(read_runtime_version));
		ext.execute_with(|| {
			let res = System::set_code(RawOrigin::Root.into(), vec![1, 2, 3, 4]);

			assert_runtime_updated_digest(if res.is_ok() { 1 } else { 0 });
			assert_eq!(expected.map_err(DispatchErrorWithPostInfo::from), res);
		});
	}
}

fn assert_runtime_updated_digest(num: usize) {
	assert_eq!(
		System::digest()
			.logs
			.into_iter()
			.filter(|item| *item == generic::DigestItem::RuntimeEnvironmentUpdated)
			.count(),
		num,
		"Incorrect number of Runtime Updated digest items",
	);
}

#[test]
fn set_code_with_real_wasm_blob() {
	let executor = substrate_test_runtime_client::new_native_or_wasm_executor();
	let mut ext = new_test_ext();
	ext.register_extension(sp_core::traits::ReadRuntimeVersionExt::new(executor));
	ext.execute_with(|| {
		System::set_block_number(1);
		System::set_code(
			RawOrigin::Root.into(),
			substrate_test_runtime_client::runtime::wasm_binary_unwrap().to_vec(),
		)
		.unwrap();

		assert_eq!(
			System::events(),
			vec![EventRecord {
				phase: Phase::Initialization,
				event: SysEvent::CodeUpdated.into(),
				topics: vec![],
			}],
		);
	});
}

#[test]
fn runtime_upgraded_with_set_storage() {
	let executor = substrate_test_runtime_client::new_native_or_wasm_executor();
	let mut ext = new_test_ext();
	ext.register_extension(sp_core::traits::ReadRuntimeVersionExt::new(executor));
	ext.execute_with(|| {
		System::set_storage(
			RawOrigin::Root.into(),
			vec![(
				well_known_keys::CODE.to_vec(),
				substrate_test_runtime_client::runtime::wasm_binary_unwrap().to_vec(),
			)],
		)
		.unwrap();
	});
}

#[test]
fn events_not_emitted_during_genesis() {
	new_test_ext().execute_with(|| {
		// Block Number is zero at genesis
		assert!(System::block_number().is_zero());
		let mut account_data = AccountInfo::default();
		System::on_created_account(Default::default(), &mut account_data);
		// No events registered at the genesis block
		assert!(!System::read_events_no_consensus().any(|_| true));
		// Events will be emitted starting on block 1
		System::set_block_number(1);
		System::on_created_account(Default::default(), &mut account_data);
		assert!(System::events().len() == 1);
	});
}

#[test]
fn extrinsics_root_is_calculated_correctly() {
	new_test_ext().execute_with(|| {
		System::reset_events();
		System::initialize(&1, &[0u8; 32].into(), &Default::default());
		System::note_finished_initialize();
		System::note_extrinsic(vec![1]);
		System::note_applied_extrinsic(&Ok(().into()), Default::default());
		System::note_extrinsic(vec![2]);
		System::note_applied_extrinsic(&Err(DispatchError::BadOrigin.into()), Default::default());
		System::note_finished_extrinsics();
		let header = System::finalize();

		let ext_root = extrinsics_data_root::<BlakeTwo256>(vec![vec![1], vec![2]]);
		assert_eq!(ext_root, *header.extrinsics_root());
	});
}

#[test]
fn runtime_updated_digest_emitted_when_heap_pages_changed() {
	new_test_ext().execute_with(|| {
		System::reset_events();
		System::initialize(&1, &[0u8; 32].into(), &Default::default());
		System::set_heap_pages(RawOrigin::Root.into(), 5).unwrap();
		assert_runtime_updated_digest(1);
	});
}

#[test]
fn ensure_signed_stuff_works() {
	struct Members;
	impl SortedMembers<u64> for Members {
		fn sorted_members() -> Vec<u64> {
			(0..10).collect()
		}
	}

	let signed_origin = RuntimeOrigin::signed(0u64);
	assert_ok!(EnsureSigned::try_origin(signed_origin.clone()));
	assert_ok!(EnsureSignedBy::<Members, _>::try_origin(signed_origin));

	#[cfg(feature = "runtime-benchmarks")]
	{
		let successful_origin: RuntimeOrigin = EnsureSigned::try_successful_origin()
			.expect("EnsureSigned has no successful origin required for the test");
		assert_ok!(EnsureSigned::try_origin(successful_origin));

		let successful_origin: RuntimeOrigin =
			EnsureSignedBy::<Members, _>::try_successful_origin()
				.expect("EnsureSignedBy has no successful origin required for the test");
		assert_ok!(EnsureSignedBy::<Members, _>::try_origin(successful_origin));
	}
}

pub fn from_actual_ref_time(ref_time: Option<u64>) -> PostDispatchInfo {
	PostDispatchInfo {
		actual_weight: ref_time.map(|t| Weight::from_all(t)),
		pays_fee: Default::default(),
	}
}

pub fn from_post_weight_info(ref_time: Option<u64>, pays_fee: Pays) -> PostDispatchInfo {
	PostDispatchInfo { actual_weight: ref_time.map(|t| Weight::from_all(t)), pays_fee }
}
