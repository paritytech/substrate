FROM phusion/baseimage:0.10.1
LABEL maintainer "chevdor@gmail.com"

ARG PROFILE=release

RUN mkdir -p polkadot && \
	apt-get update && \
	apt-get upgrade -y && \
	apt-get install -y cmake pkg-config libssl-dev git && \
	apt-get clean && \
	mkdir -p /root/.local/share/Polkadot && \
	ln -s /root/.local/share/Polkadot /data

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
	mv target/$PROFILE/polkadot /usr/local/bin && \
	cargo clean && \
	rm -rf /root/.cargo /root/.rustup /tmp/*

COPY version /polkadot
WORKDIR /polkadot
EXPOSE 30333 9933 9944
VOLUME ["/data"]

CMD ["/bin/sh", "polkadot"]
