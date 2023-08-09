// This file is part of Substrate.

// Copyright (C) 2023 Parity Technologies (UK) Ltd.
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
	///   `webrtc::peer_connection::certificate::RTCCertificate`.
	///
	/// If the file does not exist, it is created with a newly generated certificate.
	#[clap(long, value_name = "FILE")]
	pub webrtc_certificate_file: Option<PathBuf>,

	/// When set to `true`, a new WebRTC certificate will be created each time you start a node.
	///
	/// The certificate won't be stored on disk. Use this option only if you DON'T want to preserve
	/// node's WebRTC identity between (re)starts.
	///
	/// This option takes precedence over `--webrtc-certificate-file` and
	/// `--webrtc-certificate-raw` options.
	#[arg(long, value_name = "EPHEMERAL")]
	pub webrtc_certificate_ephemeral: Option<bool>,

	/// The node's WebRTC certificate to use for libp2p networking.
	///
	/// The value should be a hex encoded ASCII PEM string.
	///
	/// The value of this option takes precedence over `--webrtc-certificate-file`.
	///
	/// WARNING: Secrets provided as command-line arguments are easily exposed.
	/// Use of this option should be limited to development and testing. To use
	/// an externally managed secret key, use `--webrtc-certificate-file` instead.
	#[arg(long, value_name = "RAW")]
	pub webrtc_certificate_raw: Option<String>,
}

/// Create an error caused by an invalid webrtc certificate raw argument.
fn invalid_webrtc_certificate(e: impl std::fmt::Debug) -> error::Error {
	error::Error::Input(format!("Invalid WebRTC certificate: {:?}", e))
}

impl WebRTCCertificateParams {
	/// Create a `WebRTCConfig` from the given [`WebRTCCertificateParams`] in the context
	/// of an optional base config storage directory.
	pub fn webrtc_certificate(&self, config_dir: &PathBuf) -> error::Result<WebRTCConfig> {
		if let Some(true) = self.webrtc_certificate_ephemeral {
			// ephemeral option takes precedence over everything else
			Ok(WebRTCConfig::Ephemeral)
		} else if let Some(pem) = self.webrtc_certificate_raw.clone() {
			let bytes = array_bytes::hex2bytes(&pem).map_err(|e| invalid_webrtc_certificate(e))?;
			let s = String::from_utf8(bytes).map_err(|e| invalid_webrtc_certificate(e))?;
			Ok(WebRTCConfig::Raw(s))
		} else {
			let filename = self
				.webrtc_certificate_file
				.clone()
				.unwrap_or_else(|| config_dir.join(WEBRTC_CERTIFICATE_FILENAME));

			Ok(WebRTCConfig::File(filename))
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use libp2p_webrtc::tokio::Certificate as WebRTCCertificate;
	use rand::thread_rng;
	use std::fs;

	#[test]
	fn test_webrtc_certificate_file() {
		fn load_cert_and_assert_eq(cert_file: PathBuf, expected: WebRTCCertificate) {
			let params = WebRTCCertificateParams {
				webrtc_certificate_file: Some(cert_file),
				webrtc_certificate_ephemeral: None,
				webrtc_certificate_raw: None,
			};

			let loaded_cert = params
				.webrtc_certificate(&PathBuf::from("not-used"))
				.expect("Creates certificate config")
				.into_certificate()
				.expect("Creates certificate");

			assert_eq!(loaded_cert, expected, "expected the same certificate");
		}

		let tmp = tempfile::Builder::new().prefix("alice").tempdir().expect("Creates tempfile");
		let cert_file = tmp.path().join("mycertificate").to_path_buf();

		let cert = WebRTCCertificate::generate(&mut thread_rng()).expect("Generates certificate");
		fs::write(&cert_file, cert.serialize_pem().as_bytes()).expect("Writes certificate");

		load_cert_and_assert_eq(cert_file, cert);
	}

	#[test]
	fn test_webrtc_certificate_ephemeral() {
		let config_dir = PathBuf::from("not-used");
		let cert_file = config_dir.join(WEBRTC_CERTIFICATE_FILENAME);

		let params = WebRTCCertificateParams {
			webrtc_certificate_file: Some(cert_file.clone()),
			webrtc_certificate_ephemeral: Some(true),
			webrtc_certificate_raw: None,
		};

		let _loaded_cert = params
			.webrtc_certificate(&config_dir)
			.expect("Creates certificate config")
			.into_certificate()
			.expect("Creates certificate");

		assert!(!config_dir.exists(), "Does not create a directory");
		assert!(!cert_file.exists(), "Does not create a file");
	}

	#[test]
	fn test_webrtc_certificate_raw() {
		let config_dir = PathBuf::from("not-used");
		let cert_file = config_dir.join(WEBRTC_CERTIFICATE_FILENAME);

		let params = WebRTCCertificateParams {
			webrtc_certificate_file: None,
			webrtc_certificate_ephemeral: None,
			webrtc_certificate_raw: Some("2d2d2d2d2d424547494e20455850495245532d2d2d2d2d0d0a415066686e6738414141413d0d0a2d2d2d2d2d454e4420455850495245532d2d2d2d2d0d0a0a2d2d2d2d2d424547494e20505249564154455f4b45592d2d2d2d2d0d0a4d494748416745414d424d4742797147534d34394167454743437147534d3439417745484247307761774942415151674663347473774a657230546e47524f710d0a45497a534b506a625a3937474149463078596d50516663563967576852414e4341415374386a4f6f42452f4847493751504f56354b6471575041644d525347340d0a3569374b524f536a754d5077493658524c7079782f71693770514548796378735059532f66454f543041444f644945594a532b6e364954530d0a2d2d2d2d2d454e4420505249564154455f4b45592d2d2d2d2d0d0a0d0a2d2d2d2d2d424547494e2043455254494649434154452d2d2d2d2d0d0a4d494942574443422f36414441674543416768616d33776c41587350707a414b42676771686b6a4f50515144416a41684d523877485159445651514444425a790d0a5932646c6269427a5a57786d49484e705a32356c5a43426a5a584a304d434158445463314d4445774d5441774d4441774d466f59447a51774f5459774d5441780d0a4d4441774d444177576a41684d523877485159445651514444425a795932646c6269427a5a57786d49484e705a32356c5a43426a5a584a304d466b77457759480d0a4b6f5a497a6a3043415159494b6f5a497a6a304441516344516741457266497a714152507878694f30447a6c65536e616c6a774854455568754f5975796b546b0d0a6f376a4438434f6c305336637366366f7536554242386e4d62443245763378446b3941417a6e534247435576702b694530714d664d42307747775944565230520d0a42425177456f49514f48686a61546471544441305a47523352446c6e527a414b42676771686b6a4f5051514441674e4941444246416942764f7a3942384353540d0a367248374a364175486a577a456c704662595536776779784b69544e6a7669345a51496841493374667931794e37734f5936764455594c71566c50494f376d470d0a58335845717766524d6843744b54464c0d0a2d2d2d2d2d454e442043455254494649434154452d2d2d2d2d0d0a".to_string()),
		};

		let _loaded_cert = params
			.webrtc_certificate(&config_dir)
			.expect("Creates certificate config")
			.into_certificate()
			.expect("Creates certificate");

		assert!(!config_dir.exists(), "Does not create a directory");
		assert!(!cert_file.exists(), "Does not create a file");

		// TODO: wait until `Fingerprint` is made public
		// assert_eq!(loaded_cert.fingerprint(), Fingerprint::raw([...]));
	}
}
