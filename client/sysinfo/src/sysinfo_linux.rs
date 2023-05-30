// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

use regex::Regex;
use sc_telemetry::SysInfo;
use std::collections::HashSet;

fn read_file(path: &str) -> Option<String> {
	match std::fs::read_to_string(path) {
		Ok(data) => Some(data),
		Err(error) => {
			log::warn!("Failed to read '{}': {}", path, error);
			None
		},
	}
}

fn extract<T>(data: &str, regex: &str) -> Option<T>
where
	T: std::str::FromStr,
{
	Regex::new(regex)
		.expect("regex is correct; qed")
		.captures(&data)?
		.get(1)?
		.as_str()
		.parse()
		.ok()
}

const LINUX_REGEX_CPU: &str = r#"(?m)^model name\s*:\s*([^\n]+)"#;
const LINUX_REGEX_PHYSICAL_ID: &str = r#"(?m)^physical id\s*:\s*(\d+)"#;
const LINUX_REGEX_CORE_ID: &str = r#"(?m)^core id\s*:\s*(\d+)"#;
const LINUX_REGEX_HYPERVISOR: &str = r#"(?m)^flags\s*:.+?\bhypervisor\b"#;
const LINUX_REGEX_MEMORY: &str = r#"(?m)^MemTotal:\s*(\d+) kB"#;
const LINUX_REGEX_DISTRO: &str = r#"(?m)^PRETTY_NAME\s*=\s*"?(.+?)"?$"#;

pub fn gather_linux_sysinfo(sysinfo: &mut SysInfo) {
	if let Some(data) = read_file("/proc/cpuinfo") {
		sysinfo.cpu = extract(&data, LINUX_REGEX_CPU);
		sysinfo.is_virtual_machine =
			Some(Regex::new(LINUX_REGEX_HYPERVISOR).unwrap().is_match(&data));

		// The /proc/cpuinfo returns a list of all of the hardware threads.
		//
		// Here we extract all of the unique {CPU ID, core ID} pairs to get
		// the total number of cores.
		let mut set: HashSet<(u32, u32)> = HashSet::new();
		for chunk in data.split("\n\n") {
			let pid = extract(chunk, LINUX_REGEX_PHYSICAL_ID);
			let cid = extract(chunk, LINUX_REGEX_CORE_ID);
			if let (Some(pid), Some(cid)) = (pid, cid) {
				set.insert((pid, cid));
			}
		}

		if !set.is_empty() {
			sysinfo.core_count = Some(set.len() as u32);
		}
	}

	if let Some(data) = read_file("/proc/meminfo") {
		sysinfo.memory = extract(&data, LINUX_REGEX_MEMORY).map(|memory: u64| memory * 1024);
	}

	if let Some(data) = read_file("/etc/os-release") {
		sysinfo.linux_distro = extract(&data, LINUX_REGEX_DISTRO);
	}

	// NOTE: We don't use the `nix` crate to call this since it doesn't
	//       currently check for errors.
	unsafe {
		// SAFETY: The `utsname` is full of byte arrays, so this is safe.
		let mut uname: libc::utsname = std::mem::zeroed();
		if libc::uname(&mut uname) < 0 {
			log::warn!("uname failed: {}", std::io::Error::last_os_error());
		} else {
			let length =
				uname.release.iter().position(|&byte| byte == 0).unwrap_or(uname.release.len());
			let release = std::slice::from_raw_parts(uname.release.as_ptr().cast(), length);
			if let Ok(release) = std::str::from_utf8(release) {
				sysinfo.linux_kernel = Some(release.into());
			}
		}
	}

	match landlock::get_status() {
		Err(err) => log::warn!("landlock::get_status failed: {}", err),
		Ok(status) => sysinfo.landlock_status = Some(landlock::status_to_telemetry_string(status)),
	}
}

mod landlock {
	use landlock::{Access, AccessFs, Ruleset, RulesetAttr, RulesetError, RulesetStatus, ABI};

	// TODO: <https://github.com/landlock-lsm/rust-landlock/issues/36>
	/// Returns to what degree landlock is enabled on the current Linux environment.
	pub fn get_status() -> Result<RulesetStatus, Box<dyn std::error::Error>> {
		match std::thread::spawn(|| try_restrict_thread()).join() {
			Ok(Ok(status)) => Ok(status),
			Ok(Err(ruleset_err)) => Err(ruleset_err.into()),
			Err(_err) => Err("a panic occurred in try_restrict_thread".into()),
		}
	}

	/// Returns a single bool indicating whether landlock is fully enabled on the current Linux
	/// environment.
	pub fn is_fully_enabled() -> bool {
		matches!(get_status(), Ok(RulesetStatus::FullyEnforced))
	}

	/// Converts the [`RulesetStatus`] to a string to be used in telemetry.
	pub fn status_to_telemetry_string(status: RulesetStatus) -> String {
		match status {
			RulesetStatus::FullyEnforced => "Enabled".into(),
			RulesetStatus::PartiallyEnforced => "Partially enabled".into(),
			RulesetStatus::NotEnforced => "Disabled".into(),
		}
	}

	// NOTE: Must be kept in-sync with `landlock::try_restrict_thread` in polkadot.
	/// Tries to restrict the current thread with the following landlock access controls:
	///
	/// 1. all global filesystem access
	/// 2. ... more may be supported in the future.
	///
	/// If landlock is not supported in the current environment this is simply a noop.
	///
	/// # Returns
	///
	/// The status of the restriction (whether it was fully, partially, or not-at-all enforced).
	fn try_restrict_thread() -> Result<RulesetStatus, RulesetError> {
		let abi = ABI::V2;
		let status = Ruleset::new()
			.handle_access(AccessFs::from_all(abi))?
			.create()?
			.restrict_self()?;
		Ok(status.ruleset)
	}

	#[cfg(test)]
	mod tests {
		use super::*;
		use std::{fs, io::ErrorKind, thread};

		#[test]
		fn restricted_thread_cannot_access_fs() {
			// TODO: This would be nice: <https://github.com/rust-lang/rust/issues/68007>.
			if !is_fully_enabled() {
				return
			}

			// Restricted thread cannot read from FS.
			let handle = thread::spawn(|| {
				// Write to a tmp file, this should succeed before landlock is applied.
				let text = "foo";
				let tmpfile = tempfile::NamedTempFile::new().unwrap();
				let path = tmpfile.path();
				fs::write(path, text).unwrap();
				let s = fs::read_to_string(path).unwrap();
				assert_eq!(s, text);

				let status = super::try_restrict_thread().unwrap();
				if let RulesetStatus::NotEnforced = status {
					panic!("Ruleset should be enforced since we checked if landlock is enabled");
				}

				// Try to read from the tmp file after landlock.
				let result = fs::read_to_string(path);
				assert!(matches!(
					result,
					Err(err) if matches!(err.kind(), ErrorKind::PermissionDenied)
				));
			});

			assert!(handle.join().is_ok());

			// Restricted thread cannot write to FS.
			let handle = thread::spawn(|| {
				let text = "foo";
				let tmpfile = tempfile::NamedTempFile::new().unwrap();
				let path = tmpfile.path();

				let status = super::try_restrict_thread().unwrap();
				if let RulesetStatus::NotEnforced = status {
					panic!("Ruleset should be enforced since we checked if landlock is enabled");
				}

				// Try to write to the tmp file after landlock.
				let result = fs::write(path, text);
				assert!(matches!(
					result,
					Err(err) if matches!(err.kind(), ErrorKind::PermissionDenied)
				));
			});

			assert!(handle.join().is_ok());
		}
	}
}
