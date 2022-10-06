use assert_cmd::Command;

#[cfg(feature = "remote-test-kusama")]
const TEST_URI: &'static str = "wss://kusama-rpc.polkadot.io/";
#[cfg(feature = "remote-test-polkadot")]
const TEST_URI: &'static str = "wss://rpc.polkadot.io/";
#[cfg(not(any(feature = "remote-test-kusama", feature = "remote-test-polkadot")))]
const TEST_URI: &'static str = "ws://localhost:9944";

#[test]
fn sub_du_starts_to_scrape_normal() {
	let mut cmd = Command::cargo_bin("sub-du").unwrap();
	let stdout = cmd
		.args(&["--uri", TEST_URI, "-p"])
		.timeout(std::time::Duration::from_secs(10))
		.output()
		.unwrap()
		.stdout;

	#[cfg(feature = "remote-test-kusama")]
	assert!(String::from_utf8_lossy(&stdout).contains("of kusama("));
	#[cfg(feature = "remote-test-polkadot")]
	assert!(String::from_utf8_lossy(&stdout).contains("of polkadot("));
}
