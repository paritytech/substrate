FROM phusion/baseimage:0.10.1
LABEL maintainer "chevdor@gmail.com"

ARG PROFILE=release

RUN apt-get update && \
	apt-get upgrade -y && \
	apt-get install -y cmake pkg-config libssl-dev git

RUN curl https://sh.rustup.rs -sSf | sh -s -- -y && \
	export PATH=$PATH:$HOME/.cargo/bin && \
	rustup update nightly && \
	rustup target add wasm32-unknown-unknown --toolchain nightly && \
	rustup update stable && \
	cargo install --git https://github.com/alexcrichton/wasm-gc && \
	git clone https://github.com/paritytech/polkadot.git && \
	cd polkadot && \
	./build.sh && \
	cargo build --$PROFILE && \
	export PATH=$PATH:/polkadot/target/$PROFILE

WORKDIR /polkadot
CMD ["/bin/sh", "polkadot"]
