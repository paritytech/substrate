# Note: We don't use Alpine and its packaged Rust/Cargo because they're too often out of date,
# preventing them from being used to build Substrate/Polkadot.

FROM phusion/baseimage:0.10.2 as builder
LABEL maintainer="chevdor@gmail.com"
LABEL description="This is the build stage for Substrate. Here we create the binary."

ARG PROFILE=release
WORKDIR /substrate

COPY . /substrate

RUN apt-get update && \
	apt-get upgrade -y && \
	apt-get install -y cmake pkg-config libssl-dev git clang

RUN curl https://sh.rustup.rs -sSf | sh -s -- -y && \
	export PATH="$PATH:$HOME/.cargo/bin" && \
	rustup toolchain install nightly && \
	rustup target add wasm32-unknown-unknown --toolchain nightly && \
	cargo install --git https://github.com/alexcrichton/wasm-gc && \
	rustup default nightly && \
 	./scripts/build.sh && \
 	rustup default stable && \
	cargo build --$PROFILE

# ===== SECOND STAGE ======

FROM phusion/baseimage:0.10.2
LABEL maintainer="chevdor@gmail.com"
LABEL description="This is the 2nd stage: a very small image where we copy the Substrate binary."
ARG PROFILE=release

RUN mv /usr/share/ca* /tmp && \
	rm -rf /usr/share/*  && \
	mv /tmp/ca-certificates /usr/share/ && \
	mkdir -p /root/.local/share/Polkadot && \
	ln -s /root/.local/share/Polkadot /data && \
	useradd -m -u 1000 -U -s /bin/sh -d /substrate substrate

COPY --from=builder /substrate/target/$PROFILE/substrate /usr/local/bin

# checks
RUN ldd /usr/local/bin/substrate && \
	/usr/local/bin/substrate --version

# Shrinking
RUN rm -rf /usr/lib/python* && \
	rm -rf /usr/bin /usr/sbin /usr/share/man

USER substrate
EXPOSE 30333 9933 9944
VOLUME ["/data"]

CMD ["/usr/local/bin/substrate"]
