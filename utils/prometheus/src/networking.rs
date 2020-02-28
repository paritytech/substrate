// Copyright 2019-2020 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

use async_std::pin::Pin;
use std::task::{Poll, Context};
use futures_util::{stream::Stream, io::{AsyncRead, AsyncWrite}};

pub struct Incoming<'a>(pub async_std::net::Incoming<'a>);

impl hyper::server::accept::Accept for Incoming<'_> {
	type Conn = TcpStream;
	type Error = async_std::io::Error;

	fn poll_accept(self: Pin<&mut Self>, cx: &mut Context) -> Poll<Option<Result<Self::Conn, Self::Error>>> {
		Pin::new(&mut Pin::into_inner(self).0)
			.poll_next(cx)
			.map(|opt| opt.map(|res| res.map(TcpStream)))
	}
}

pub struct TcpStream(pub async_std::net::TcpStream);

impl tokio::io::AsyncRead for TcpStream {
	fn poll_read(
		self: Pin<&mut Self>,
		cx: &mut Context,
		buf: &mut [u8]
	) -> Poll<Result<usize, std::io::Error>> {
		Pin::new(&mut Pin::into_inner(self).0)
			.poll_read(cx, buf)
	}
}

impl tokio::io::AsyncWrite for TcpStream {
	fn poll_write(
		self: Pin<&mut Self>,
		cx: &mut Context,
		buf: &[u8]
	) -> Poll<Result<usize, std::io::Error>> {
		Pin::new(&mut Pin::into_inner(self).0)
			.poll_write(cx, buf)
	}

	fn poll_flush(self: Pin<&mut Self>, cx: &mut Context) -> Poll<Result<(), std::io::Error>> {
		Pin::new(&mut Pin::into_inner(self).0)
			.poll_flush(cx)
	}

	fn poll_shutdown(self: Pin<&mut Self>, cx: &mut Context) -> Poll<Result<(), std::io::Error>> {
		Pin::new(&mut Pin::into_inner(self).0)
			.poll_close(cx)
	}
}
