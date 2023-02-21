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
}
