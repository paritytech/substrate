use super::{Event as SignedEvent, *};
use crate::mock::*;

mod calls {
	use frame_support::bounded_vec;

	use super::*;

	#[test]
	fn register_metadata_works() {
		ExtBuilder::signed().build_and_execute(|| {
			roll_to_signed_open();
			assert_full_snapshot();

			assert_eq!(balances(99), (100, 0));
			let score = ElectionScore { minimal_stake: 100, ..Default::default() };

			assert_ok!(SignedPallet::register(Origin::signed(99), score));
			assert_eq!(balances(99), (95, 5));

			assert_eq!(Submissions::<Runtime>::metadata_iter(1).count(), 0);
			assert_eq!(Submissions::<Runtime>::metadata_iter(0).count(), 1);
			assert_eq!(
				Submissions::<Runtime>::metadata_of(0, 99).unwrap(),
				SubmissionMetadata {
					claimed_score: score,
					deposit: 5,
					fee: 1,
					pages: bounded_vec![false, false, false],
					reward: 3
				}
			);
			assert_eq!(
				*Submissions::<Runtime>::leaderboard(0),
				vec![(99, ElectionScore { minimal_stake: 100, ..Default::default() })]
			);
			assert!(matches!(signed_events().as_slice(), &[
					SignedEvent::Registered(_, x, _),
				] if x == 99));

			// second ones submits
			assert_eq!(balances(999), (100, 0));
			let score = ElectionScore { minimal_stake: 90, ..Default::default() };
			assert_ok!(SignedPallet::register(Origin::signed(999), score));
			assert_eq!(balances(999), (95, 5));
			assert_eq!(
				Submissions::<Runtime>::metadata_of(0, 999).unwrap(),
				SubmissionMetadata {
					claimed_score: score,
					deposit: 5,
					fee: 1,
					pages: bounded_vec![false, false, false],
					reward: 3
				}
			);
			assert!(matches!(signed_events().as_slice(), &[
					SignedEvent::Registered(..),
					SignedEvent::Registered(_, x, _),
				] if x == 999));

			assert_eq!(
				*Submissions::<Runtime>::leaderboard(0),
				vec![
					(999, ElectionScore { minimal_stake: 90, ..Default::default() }),
					(99, ElectionScore { minimal_stake: 100, ..Default::default() })
				]
			);
			assert_eq!(Submissions::<Runtime>::metadata_iter(1).count(), 0);
			assert_eq!(Submissions::<Runtime>::metadata_iter(0).count(), 2);

			// submit again with a new score.
			assert_noop!(
				SignedPallet::register(
					Origin::signed(999),
					ElectionScore { minimal_stake: 80, ..Default::default() }
				),
				"Duplicate",
			);
		})
	}

	#[test]
	fn metadata_submission_sorted_based_on_stake() {
		ExtBuilder::signed().build_and_execute(|| {
			roll_to_signed_open();
			assert_full_snapshot();

			let score_from = |x| ElectionScore { minimal_stake: x, ..Default::default() };
			let assert_reserved = |x| assert_eq!(balances(x), (95, 5));
			let assert_unreserved = |x| assert_eq!(balances(x), (100, 0));

			assert_ok!(SignedPallet::register(Origin::signed(91), score_from(100)));
			assert_eq!(*Submissions::<Runtime>::leaderboard(0), vec![(91, score_from(100))]);
			assert_reserved(91);
			assert!(
				matches!(signed_events().as_slice(), &[SignedEvent::Registered(_, x, _)] if x == 91)
			);

			// weaker one comes while we have space.
			assert_ok!(SignedPallet::register(Origin::signed(92), score_from(90)));
			assert_eq!(
				*Submissions::<Runtime>::leaderboard(0),
				vec![(92, score_from(90)), (91, score_from(100))]
			);
			assert_reserved(92);
			assert!(matches!(signed_events().as_slice(), &[
					SignedEvent::Registered(..),
					SignedEvent::Registered(_, x, _),
				] if x == 92));

			// stronger one comes while we have have space.
			assert_ok!(SignedPallet::register(Origin::signed(93), score_from(110)));
			assert_eq!(
				*Submissions::<Runtime>::leaderboard(0),
				vec![(92, score_from(90)), (91, score_from(100)), (93, score_from(110))]
			);
			assert_reserved(93);
			assert!(matches!(signed_events().as_slice(), &[
					SignedEvent::Registered(..),
					SignedEvent::Registered(..),
					SignedEvent::Registered(_, x, _),
				] if x == 93));

			// weaker one comes while we don't have space.
			assert_noop!(SignedPallet::register(Origin::signed(94), score_from(80)), "QueueFull");
			assert_eq!(
				*Submissions::<Runtime>::leaderboard(0),
				vec![(92, score_from(90)), (91, score_from(100)), (93, score_from(110))]
			);
			assert_unreserved(94);
			// no event has been emitted this time.
			assert!(matches!(
				signed_events().as_slice(),
				&[
					SignedEvent::Registered(..),
					SignedEvent::Registered(..),
					SignedEvent::Registered(..),
				]
			));

			// stronger one comes while we don't have space. Eject the weakest
			assert_ok!(SignedPallet::register(Origin::signed(94), score_from(120)));
			assert_eq!(
				*Submissions::<Runtime>::leaderboard(0),
				vec![(91, score_from(100)), (93, score_from(110)), (94, score_from(120))]
			);
			assert_reserved(94);
			assert_unreserved(92);
			assert!(matches!(
				signed_events().as_slice(),
				&[
					SignedEvent::Registered(..),
					SignedEvent::Registered(..),
					SignedEvent::Registered(..),
					SignedEvent::Discarded(_, 92),
					SignedEvent::Registered(_, 94, _),
				]
			));

			// another stronger one comes, only replace the weakest.
			assert_ok!(SignedPallet::register(Origin::signed(95), score_from(105)));
			assert_eq!(
				*Submissions::<Runtime>::leaderboard(0),
				vec![(95, score_from(105)), (93, score_from(110)), (94, score_from(120))]
			);
			assert_reserved(95);
			assert_unreserved(91);
			assert!(matches!(
				signed_events().as_slice(),
				&[
					SignedEvent::Registered(..),
					SignedEvent::Registered(..),
					SignedEvent::Registered(..),
					SignedEvent::Discarded(..),
					SignedEvent::Registered(..),
					SignedEvent::Discarded(_, 91),
					SignedEvent::Registered(_, 95, _),
				]
			));
		})
	}

	#[test]
	fn can_bail_at_a_cost() {
		ExtBuilder::signed().build_and_execute(|| {
			roll_to_signed_open();
			assert_full_snapshot();

			assert_ok!(SignedPallet::register(
				Origin::signed(99),
				ElectionScore { minimal_stake: 100, ..Default::default() }
			));
			assert_eq!(balances(99), (95, 5));

			// not submitted, cannot bailout.
			assert_noop!(SignedPallet::bail(Origin::signed(999)), "NoSubmission");

			// can bail.
			assert_ok!(SignedPallet::bail(Origin::signed(99)));
			// 20% of the deposit returned, which is 1, 4 is slashed.
			assert_eq!(balances(99), (96, 0));
			assert_no_data_for(0, 99);

			assert!(matches!(
				dbg!(signed_events()).as_slice(),
				&[SignedEvent::Registered(..), SignedEvent::Bailed(..)]
			));
		});
	}

	#[test]
	fn can_submit_pages() {
		ExtBuilder::signed().build_and_execute(|| {
			roll_to_signed_open();
			assert_full_snapshot();

			assert_noop!(
				SignedPallet::submit_page(Origin::signed(99), 0, Default::default()),
				"NotRegistered"
			);

			assert_ok!(SignedPallet::register(
				Origin::signed(99),
				ElectionScore { minimal_stake: 100, ..Default::default() }
			));

			assert_noop!(
				SignedPallet::submit_page(Origin::signed(99), 3, Default::default()),
				"BadPageIndex"
			);
			assert_noop!(
				SignedPallet::submit_page(Origin::signed(99), 4, Default::default()),
				"BadPageIndex"
			);

			assert_eq!(Submissions::<Runtime>::pages_of(0, 99).count(), 0);
			assert_eq!(balances(99), (95, 5));

			// add the first page.
			assert_ok!(SignedPallet::submit_page(Origin::signed(99), 0, Some(Default::default())));
			assert_eq!(Submissions::<Runtime>::pages_of(0, 99).count(), 1);
			assert_eq!(balances(99), (94, 6));
			assert_eq!(
				Submissions::<Runtime>::metadata_of(0, 99).unwrap().pages.into_inner(),
				vec![true, false, false]
			);

			// replace it again, nada.
			assert_ok!(SignedPallet::submit_page(Origin::signed(99), 0, Some(Default::default())));
			assert_eq!(Submissions::<Runtime>::pages_of(0, 99).count(), 1);
			assert_eq!(balances(99), (94, 6));

			// add a new one.
			assert_ok!(SignedPallet::submit_page(Origin::signed(99), 1, Some(Default::default())));
			assert_eq!(Submissions::<Runtime>::pages_of(0, 99).count(), 2);
			assert_eq!(balances(99), (93, 7));
			assert_eq!(
				Submissions::<Runtime>::metadata_of(0, 99).unwrap().pages.into_inner(),
				vec![true, true, false]
			);

			// remove one, deposit is back.
			assert_ok!(SignedPallet::submit_page(Origin::signed(99), 0, None));
			assert_eq!(Submissions::<Runtime>::pages_of(0, 99).count(), 1);
			assert_eq!(balances(99), (94, 6));
			assert_eq!(
				Submissions::<Runtime>::metadata_of(0, 99).unwrap().pages.into_inner(),
				vec![false, true, false]
			);

			assert!(matches!(
				signed_events().as_slice(),
				&[
					SignedEvent::Registered(..),
					SignedEvent::Stored(.., 0),
					SignedEvent::Stored(.., 0),
					SignedEvent::Stored(.., 1),
					SignedEvent::Stored(.., 0),
				]
			));
		});
	}
}

mod e2e {
	use frame_election_provider_support::Support;

	use super::*;
	#[test]
	fn good_bad_evil() {
		// an extensive scenario: 3 solutions submitted, once rewarded, one slashed, and one
		// discarded.
		ExtBuilder::signed().build_and_execute(|| {
			roll_to_signed_open();
			assert_full_snapshot();

			// a valid, but weak solution.
			{
				let score =
					ElectionScore { minimal_stake: 10, sum_stake: 10, sum_stake_squared: 100 };
				assert_ok!(SignedPallet::register(Origin::signed(99), score));
				assert_ok!(SignedPallet::submit_page(
					Origin::signed(99),
					0,
					Some(Default::default())
				));

				assert_eq!(balances(99), (94, 6));
			}

			// a valid, strong solution.
			let strong_score = {
				let paged = mine_full_solution().unwrap();
				load_signed_for_verification(999, paged.clone());
				assert_eq!(balances(999), (92, 8));
				paged.score
			};

			// an invalid, strong solution.
			{
				let mut score = strong_score;
				score.minimal_stake *= 2;
				assert_ok!(SignedPallet::register(Origin::signed(92), score));
				assert_eq!(balances(92), (95, 5));
				// we don't even bother to submit a page..
			}

			assert_eq!(
				Submissions::<Runtime>::leaderboard(0)
					.into_iter()
					.map(|(x, _)| x)
					.collect::<Vec<_>>(),
				vec![99, 999, 92]
			);

			roll_to_signed_validation_open();

			// 92 is slashed in 3 blocks, 999 becomes rewarded in 3 blocks, , and 99 is discarded.
			roll_next();
			roll_next();
			roll_next();

			assert_eq!(
				Submissions::<Runtime>::leaderboard(0)
					.into_iter()
					.map(|(x, _)| x)
					.collect::<Vec<_>>(),
				vec![99, 999]
			);

			roll_next();
			roll_next();
			roll_next();

			assert!(matches!(
				signed_events().as_slice(),
				&[
					SignedEvent::Registered(..),
					SignedEvent::Stored(..),
					SignedEvent::Registered(..),
					SignedEvent::Stored(..),
					SignedEvent::Stored(..),
					SignedEvent::Stored(..),
					SignedEvent::Registered(..),
					SignedEvent::Slashed(0, 92, ..),
					SignedEvent::Rewarded(0, 999, 4), // 3 reward + 1 tx-fee
					SignedEvent::Discarded(0, 99),
				]
			));

			assert_eq!(balances(99), (100, 0));
			assert_eq!(balances(999), (104, 0));
			assert_eq!(balances(92), (95, 0));

			// signed pallet should be in 100% clean state.
			assert_ok!(Submissions::<Runtime>::ensure_killed(0));
		})
	}
}
