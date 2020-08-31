use crate as datafeed;
use crate::*;
use codec::{Decode, Encode};
use frame_support::{
	assert_ok, impl_outer_event, impl_outer_origin, parameter_types, traits::OnFinalize,
	weights::Weight,
};
use frame_system::{EnsureOneOf, EnsureRoot, EnsureSignedBy};
use sp_core::{
	offchain::{testing, OffchainExt, TransactionPoolExt},
	sr25519::Signature,
	testing::KeyStore,
	traits::KeystoreExt,
	H256,
};
use sp_runtime::{
	testing::{Header, TestXt},
	traits::{BlakeTwo256, Extrinsic as ExtrinsicT, IdentifyAccount, IdentityLookup, Verify},
	FixedU128, Perbill, RuntimeAppPublic,
};

impl_outer_origin! {
	pub enum Origin for Test where system = frame_system {}
}

impl_outer_event! {
	pub enum TestEvent for Test {
		frame_system<T>,
		datafeed<T>,
	}
}

#[derive(Clone, Eq, PartialEq, Encode, Decode)]
pub struct Test;
parameter_types! {
	pub const BlockHashCount: u64 = 250;
	pub const MaximumBlockWeight: Weight = 1024;
	pub const MaximumBlockLength: u32 = 2 * 1024;
	pub const AvailableBlockRatio: Perbill = Perbill::one();
}
impl frame_system::Trait for Test {
	type BaseCallFilter = ();
	type Origin = Origin;
	type Call = ();
	type Index = u64;
	type BlockNumber = u64;
	type Hash = H256;
	type Hashing = BlakeTwo256;
	type AccountId = sp_core::sr25519::Public;
	type Lookup = IdentityLookup<Self::AccountId>;
	type Header = Header;
	type Event = TestEvent;
	type BlockHashCount = BlockHashCount;
	type MaximumBlockWeight = MaximumBlockWeight;
	type DbWeight = ();
	type BlockExecutionWeight = ();
	type ExtrinsicBaseWeight = ();
	type MaximumExtrinsicWeight = MaximumBlockWeight;
	type MaximumBlockLength = MaximumBlockLength;
	type AvailableBlockRatio = AvailableBlockRatio;
	type Version = ();
	type ModuleToIndex = ();
	type AccountData = ();
	type OnNewAccount = ();
	type OnKilledAccount = ();
	type SystemWeightInfo = ();
}

type Extrinsic = TestXt<Call<Test>, ()>;
type AccountId = <<Signature as Verify>::Signer as IdentifyAccount>::AccountId;

impl frame_system::offchain::SigningTypes for Test {
	type Public = <Signature as Verify>::Signer;
	type Signature = Signature;
}

impl<LocalCall> frame_system::offchain::SendTransactionTypes<LocalCall> for Test
where
	Call<Test>: From<LocalCall>,
{
	type OverarchingCall = Call<Test>;
	type Extrinsic = Extrinsic;
}

impl<LocalCall> frame_system::offchain::CreateSignedTransaction<LocalCall> for Test
where
	Call<Test>: From<LocalCall>,
{
	fn create_transaction<C: frame_system::offchain::AppCrypto<Self::Public, Self::Signature>>(
		call: Call<Test>,
		_public: <Signature as Verify>::Signer,
		_account: AccountId,
		nonce: u64,
	) -> Option<(Call<Test>, <Extrinsic as ExtrinsicT>::SignaturePayload)> {
		Some((call, (nonce, ())))
	}
}
parameter_types! {
	pub storage StorageArgument: DataType = DataType::U128(0);
}

type DataFeedOrigin =
	EnsureOneOf<AccountId, EnsureSignedBy<DataFeed, AccountId>, EnsureRoot<AccountId>>;

impl Trait for Test {
	type Event = TestEvent;
	type AuthorityId = crypto::Sr25519DataFeedAuthId;
	// frame_system::EnsureSignedBy<DataFeed, AccountId>; use this in runtime/lib.rs
	type DataFeedOrigin = DataFeedOrigin;
	type WeightInfo = ();
}

pub type System = frame_system::Module<Test>;
pub type DataFeed = Module<Test>;

#[derive(Default)]
pub struct ExtBuilder;
impl ExtBuilder {
	pub fn build(self) -> sp_io::TestExternalities {
		let t = frame_system::GenesisConfig::default()
			.build_storage::<Test>()
			.unwrap();
		let mut ext = sp_io::TestExternalities::new(t);
		ext.execute_with(|| System::set_block_number(1));
		ext
	}
}

#[test]
fn should_submit_signed_data_on_chain() {
	const PHRASE: &str =
		"news slush supreme milk chapter athlete soap sausage put clutch what kitten";

	let (offchain, offchain_state) = testing::TestOffchainExt::new();
	let (pool, pool_state) = testing::TestTransactionPoolExt::new();
	let keystore = KeyStore::new();
	keystore
		.write()
		.sr25519_generate_new(
			datafeed::crypto::Public::ID,
			Some(&format!("{}/hunter1", PHRASE)),
		)
		.unwrap();

	let mut t = ExtBuilder::default().build();
	t.register_extension(OffchainExt::new(offchain));
	t.register_extension(TransactionPoolExt::new(pool));
	t.register_extension(KeystoreExt(keystore.clone()));

	let public_key = keystore
		.read()
		.sr25519_public_keys(datafeed::crypto::Public::ID)
		.get(0)
		.unwrap()
		.clone();

	{
		let mut state = offchain_state.write();

		state.expect_request(testing::PendingRequest {
			method: "GET".into(),
			uri: "https://min-api.cryptocompare.com/data/price?fsym=BTC&tsyms=USD".into(),
			response: Some(br#"{"USD": 1.56}"#.to_vec()),
			sent: true,
			..Default::default()
		});
	}

	t.execute_with(|| {
		register_info();

		assert_ok!(DataFeed::add_provider(
			frame_system::RawOrigin::Root.into(),
			public_key
		));

		assert!(DataFeed::all_providers().contains(&public_key));

		DataFeed::fetch_and_send_signed(&StorageArgument::key().to_vec()).unwrap();

		let tx = pool_state.write().transactions.pop().unwrap();
		assert!(pool_state.read().transactions.is_empty());
		let tx = Extrinsic::decode(&mut &*tx).unwrap();
		assert_eq!(tx.signature.unwrap().0, 0);
		assert_eq!(
			tx.call,
			Call::feed_data(
				StorageArgument::key().to_vec(),
				super::DataType::FixedU128(FixedU128::from((156, 100)))
			)
		);
		let (k, data) = match tx.call {
			Call::feed_data(a, b) => (a, b),
			_ => unreachable!("must be feed_data call"),
		};

		// execute call
		DataFeed::feed_data(frame_system::RawOrigin::Signed(public_key).into(), k, data).unwrap();

		System::set_block_number(2);
		DataFeed::on_finalize(System::block_number());

		assert_eq!(
			StorageArgument::get().into_fixed_u128(),
			Some(FixedU128::from((156, 100)))
		);
	});
}

pub fn register_info() {
	let data_info = super::FeededDataInfo {
		key_str: "USD".as_bytes().to_vec(),
		number_type: NumberType::FixedU128,
		operation: Operations::Average,
		schedule: 2,
	};

	assert_ok!(DataFeed::register_storage_key(
		frame_system::RawOrigin::Root.into(),
		StorageArgument::key().to_vec(),
		data_info
	));

	assert_ok!(DataFeed::set_url(
		frame_system::RawOrigin::Root.into(),
		StorageArgument::key().to_vec(),
		b"https://min-api.cryptocompare.com/data/price?fsym=BTC&tsyms=USD".to_vec()
	));

	assert_ok!(DataFeed::set_offchain_period(
		frame_system::RawOrigin::Root.into(),
		StorageArgument::key().to_vec(),
		Some(1),
	));
}
