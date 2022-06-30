// This file is part of Substrate.

// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
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

use clap::Args;
use sc_network::config::WebRTCConfig;
use std::path::PathBuf;

use crate::error;

/// The file name of the WebRTC's certificate inside the chain-specific
/// network config directory.
const WEBRTC_CERTIFICATE_FILENAME: &str = "webrtc_certificate";

/// Parameters used to create the `WebRTCConfig`, which determines the certificate used
/// for libp2p WebRTC transport.
#[derive(Debug, Clone, Args)]
pub struct WebRTCCertificateParams {
	/// The file from which to read the node's WebRTC certificate to use for libp2p networking.
	///
	/// The contents of the file are parsed as follows:
	///
	///   The file must contain an ASCII PEM encoded
	/// [`webrtc::peer_connection::certificate::RTCCertificate`].
	///
	/// If the file does not exist, it is created with a newly generated certificate.
	#[clap(long, value_name = "FILE")]
	pub webrtc_certificate_file: Option<PathBuf>,

	/// When set to `true`, a new WebRTC certificate will be created each time you start a node.
	///
	/// The certificate won't be stored on disk. Use this option only if you DON'T want to preserve
	/// node's WebRTC identity between (re)starts.
	///
	/// This option takes precedence over `--webrtc-certificate-file` option.
	#[arg(long, value_name = "EPHEMERAL")]
	pub webrtc_certificate_ephemeral: Option<bool>,
}

impl WebRTCCertificateParams {
	/// Create a `WebRTCConfig` from the given `WebRTCCertificateParams` in the context
	/// of an optional network config storage directory.
	pub fn webrtc_certificate(&self, net_config_dir: &PathBuf) -> error::Result<WebRTCConfig> {
		if let Some(true) = self.webrtc_certificate_ephemeral {
			return Ok(WebRTCConfig::Ephemeral)
		}

		let filename = self
			.webrtc_certificate_file
			.clone()
			.unwrap_or_else(|| net_config_dir.join(WEBRTC_CERTIFICATE_FILENAME));

		Ok(WebRTCConfig::File(filename))
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use libp2p::webrtc::tokio::Certificate as WebRTCCertificate;
	use rand::thread_rng;
	use std::fs;

	#[test]
	fn test_webrtc_certificate_file() {
		fn load_cert_and_assert_eq(file: PathBuf, cert: &WebRTCCertificate) {
			let params = WebRTCCertificateParams { webrtc_certificate_file: Some(file) };

			let loaded_cert = params
				.webrtc_certificate(&PathBuf::from("not-used"))
				.expect("Creates certificate config")
				.into_certificate()
				.expect("Creates certificate");

			assert_eq!(cert, loaded_cert, "expected the same certificate");
		}

		let tmp = tempfile::Builder::new().prefix("alice").tempdir().expect("Creates tempfile");
		let file = tmp.path().join("mycertificate").to_path_buf();

		let cert = WebRTCCertificate::generate(&mut thread_rng()).expect("Generates certificate");

		fs::write(&file, cert.serialize_pem().as_bytes()).expect("Writes certificate");
		load_cert_and_assert_eq(file.clone(), &cert);
	}

	#[test]
	fn test_webrtc_certificate_ephemeral() {
		let filepath = PathBuf::from("not-used");
		let params = WebRTCCertificateParams {
			webrtc_certificate_ephemeral: Some(true),
			webrtc_certificate_file: Some(&filepath),
		};

		let _loaded_cert = params
			.webrtc_certificate(&filepath)
			.expect("Creates certificate config")
			.into_certificate()
			.expect("Creates certificate");

		assert!(!filepath.exists(), "Does not create a file");
		assert!(!filepath.join(WEBRTC_CERTIFICATE_FILENAME).exists(), "Does not create a file");
	}
}
