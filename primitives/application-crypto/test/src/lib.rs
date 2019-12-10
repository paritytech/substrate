
use sp_runtime::{generic::BlockId, traits::ProvideRuntimeApi};
use primitives::{testing::{KeyStore, ED25519}, crypto::Pair};
use test_client::{
    TestClientBuilder, DefaultTestClientBuilderExt, TestClientBuilderExt,
    runtime::{TestAPI, app_crypto::ed25519::{AppPair, AppPublic}},
};

#[test]
fn ed25519_works_in_runtime() {
    let keystore = KeyStore::new();
    let test_client = TestClientBuilder::new().set_keystore(keystore.clone()).build();
    let (signature, public) = test_client.runtime_api()
        .test_ed25519_crypto(&BlockId::Number(0))
        .expect("Tests `ed25519` crypto.");

    let key_pair = keystore.read().ed25519_key_pair(ED25519, &public.as_ref())
        .expect("There should be at a `ed25519` key in the keystore for the given public key.");

    assert!(AppPair::verify(&signature, "ed25519", &AppPublic::from(key_pair.public())));
}