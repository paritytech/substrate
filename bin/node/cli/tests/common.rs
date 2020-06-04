// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
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

#![cfg(unix)]

use std::{
	path::Path,
	ffi::OsStr,
	time::Duration,
	str::FromStr,
};
use core::{
	task::{Context, Poll},
	future::Future,
	pin::Pin,
};
use std::env::{var, VarError};
use std::process::{Stdio, ExitStatus};
use assert_cmd::cargo::cargo_bin;
use tempfile::TempDir;
use futures::{
	task::noop_waker,
	compat::Future01CompatExt
};
use tokio::{
	process::{Command, Child, ChildStdout, ChildStderr},
	io::{BufReader, Lines, AsyncBufReadExt}
};
use nix::{
	unistd::Pid,
	sys::signal::{kill, Signal}
};

use jsonrpc_core_client::{
	transports::http, RpcChannel,
};


pub struct LocalClient {
	process: Child,
	stdout: Lines<BufReader<ChildStdout>>,
	stderr: Lines<BufReader<ChildStderr>>,
	cwd: TempDir,
}

impl LocalClient {
	pub fn new<I, S>(args: I) -> Self
	where
    	I: IntoIterator<Item = S>,
		S: AsRef<OsStr>,
	{
		// FIXME: randomize port
		let temp_dir = TempDir::new().expect("Failed to create temp dir");
		let mut process = Command::new(cargo_bin("substrate"))
			.kill_on_drop(true)
			.stdout(Stdio::piped())
			.stderr(Stdio::piped())
			.args(&["--dev", "--rpc-port", "9933"])
			.arg("-d")
			.arg(temp_dir.path())
			.args(args)
			.spawn()
			.expect("Running substrate node failed.");
		let stdout = BufReader::new(process.stdout.take()
				.expect("Has stdout, we just gave it."))
			.lines();
		let stderr = BufReader::new(process.stderr.take()
				.expect("Has stderr, we just gave it."))
			.lines();
		
		LocalClient {
			process, stdout, stderr, cwd:temp_dir
		}
	}

	pub fn stdout(&mut self) -> &mut Lines<BufReader<ChildStdout>> {
		&mut self.stdout
	}

	pub fn stderr(&mut self) -> &mut Lines<BufReader<ChildStderr>> {
		&mut self.stderr
	}

	pub fn temp_dir(&self) -> &TempDir {
		&self.cwd
	}

	pub fn path(&self) -> &Path {
		self.cwd.path()
	}

	pub fn pid(&self) -> i32 {
		self.process.id() as i32
	}

	pub fn signal(&self, s: Signal) -> Result<(), nix::Error>  {
		let pid = self.pid();
		kill(Pid::from_raw(pid), s)
	}

	/// Pause the execution by `s` seconds, ensures the process is still
	/// alive after
	pub async fn run_for(&mut self, s: u64) -> Result<(),  Box<dyn std::error::Error>>  {
		tokio::time::delay_for(Duration::from_secs(s)).await;
		if self.is_alive() {
			Ok(())
		}  else {
			Err("Process died".into())
		}
	}

	/// Wait until you've seen a particular output
	/// Namely, `F` is invoked on every line give to the output
	/// and is looped until `F` returns true;
	pub async fn wait_until_seen<F>(&mut self, predicate: F) -> Result<String, Box<dyn std::error::Error>>
		where F: Fn(&String) -> bool
	{
		let reader = &mut self.stderr;
		while let Some(line) = reader.next_line().await? {
			println!("{}", line);
			if predicate(&line) {
				return Ok(line)
			}
		}

		Err("Line not found.".into())
	}

	pub async fn wait_until_imported(&mut self, num: u32)
		-> Result<(), Box<dyn std::error::Error>>
	{
		self.wait_until_seen(|l| {
			if l.contains("✨ Imported #") {
				let mut spl = l.rsplit(" ");
				spl.next(); // drop the hash
				let cur_block =  u32::from_str(&spl
					.next().expect("Number is given")[1..]
				).expect("Number can be parsed");
				if cur_block >= num {
					return true
				}
			}
			return false
		}).await.map(|_| ())
	}

	/// Gives us the exist status, if the process has ended until now.
	pub fn exit_status(&mut self) -> Option<ExitStatus> {
		match Pin::new(&mut self.process).poll(&mut Context::from_waker(&noop_waker())) {
			Poll::Ready(Ok(e)) => Some(e),
			_ => None
		}
	}

	/// Helper to know whether the process has ended yet
	pub fn is_alive(&mut self) -> bool {
		self.exit_status().is_none()
	}

	/// Wait for the process to end for a max of `s` seconds.
	/// Checks every second whether the processs has exited and returns the number
	/// of seconds it took.
	pub async fn wait_to_die(&mut self, s: u32) -> Result<u32, Box<dyn std::error::Error>> {
		let mut round = 0u32;
		loop {

			if !self.is_alive() {
				return Ok(round)
			}
			
			if round == s {
				return Err(
					format!("timed out. Process still alive after {} seconds",
							round).into()
					)
			}

			round += 1;
			tokio::time::delay_for(Duration::from_secs(1)).await
		}
	}

	pub fn kill(self) -> TempDir {
		let cwd = self.cwd;

		// we are starting it with "kill_on_drop", so this
		// will kill the subprocess
		drop(self.process);

		cwd
	}
}

enum InnerClient {
	External,
	Internal(LocalClient)
}

pub fn start_local_dev_node() -> LocalClient {
	LocalClient::new(Vec::<&OsStr>::new())
} 


pub struct BlackBoxClient(InnerClient, RpcChannel);

impl BlackBoxClient {
	pub async fn new<I, S>(args: I) -> Result<Self, Box<dyn std::error::Error>>
	where
    	I: IntoIterator<Item = S>,
		S: AsRef<OsStr>, 
	{
		let (inner, uri) = match var("EXTERNAL_NODE_RPC_ADDRESS") {
			Ok(uri) => (InnerClient::External, uri),
			Err(err) => {
				if let VarError::NotUnicode(_) = err {
					println!("$EXTERNAL_NODE_RPC_ADDRESS contains invalid unicode characters. ignoring");
				}

				let mut inner = LocalClient::new(args);
				let line = inner.wait_until_seen(|l| l.contains("📠 RPC")).await?;
				// read the address the server is available at.
				let target_url = format!("http://{}", line
					.rsplit(" ") // last value is the addr
					.next()
					.expect("URL is given")
				);
				// and we wait until production is happening
				inner.wait_until_imported(1).await?;
				(InnerClient::Internal(inner), target_url)
			}
		};

		println!("Connecting to {:?}", uri);
		let client = http::connect(&uri)
			.compat()
			.await
			.expect("Connecting via RPC failed");

		Ok(BlackBoxClient (inner, client))
	}

	pub async fn default() -> Result<Self, Box<dyn std::error::Error>> {
		Self::new(Vec::<&OsStr>::new()).await
	}

}

impl BlackBoxClient {
	// Get the RPC client
	pub fn rpc<C: From<RpcChannel>>(&self) -> C {
		C::from(self.1.clone())
	}
}
