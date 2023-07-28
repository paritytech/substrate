# This is the build stage for Substrate. Here we create the binary.
FROM docker.io/paritytech/ci-linux:production as builder

WORKDIR /substrate
COPY . /substrate
RUN cargo build --locked --release

# This is the 2nd stage: a very small image where we copy the Substrate binary."
FROM docker.io/library/ubuntu:20.04
LABEL description="Multistage Docker image for Substrate: a platform for web3" \
	io.parity.image.type="builder" \
	io.parity.image.authors="chevdor@gmail.com, devops-team@parity.io" \
	io.parity.image.vendor="Parity Technologies" \
	io.parity.image.description="Substrate is a next-generation framework for blockchain innovation 🚀" \
	io.parity.image.source="https://github.com/paritytech/polkadot/blob/${VCS_REF}/docker/substrate_builder.Dockerfile" \
	io.parity.image.documentation="https://github.com/paritytech/polkadot/"

COPY --from=builder /substrate/target/release/substrate /usr/local/bin
COPY --from=builder /substrate/target/release/subkey /usr/local/bin
COPY --from=builder /substrate/target/release/node-template /usr/local/bin
COPY --from=builder /substrate/target/release/chain-spec-builder /usr/local/bin

RUN useradd -m -u 1000 -U -s /bin/sh -d /substrate substrate && \
	mkdir -p /data /substrate/.local/share/substrate && \
	chown -R substrate:substrate /data && \
	ln -s /data /substrate/.local/share/substrate && \
# Sanity checks
	ldd /usr/local/bin/substrate && \
# unclutter and minimize the attack surface
	rm -rf /usr/bin /usr/sbin && \
	/usr/local/bin/substrate --version

USER substrate
EXPOSE 30333 9933 9944 9615
VOLUME ["/data"]
