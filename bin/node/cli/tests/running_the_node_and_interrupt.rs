use assert_cmd::cargo::cargo_bin;
use std::process::Command;
use std::thread::sleep;
use std::time::Duration;

#[test]
#[cfg(unix)]
fn running_the_node_works_and_can_be_interrupted() {
	use libc::{kill, SIGINT, SIGTERM};

	let mut cmd = Command::new(cargo_bin("substrate")).spawn().unwrap();
	sleep(Duration::from_secs(30));
	assert!(cmd.try_wait().unwrap().is_none(), "the process should still be running");
	unsafe { kill(cmd.id() as i32, SIGINT) };
	assert!(cmd.wait().unwrap().success(), "the process must exit gracefully after SIGINT");

	let mut cmd = Command::new(cargo_bin("substrate")).spawn().unwrap();
	sleep(Duration::from_secs(30));
	assert!(cmd.try_wait().unwrap().is_none(), "the process should still be running");
	unsafe { kill(cmd.id() as i32, SIGTERM) };
	assert!(cmd.wait().unwrap().success(), "the process must exit gracefully after SIGTERM");
}
