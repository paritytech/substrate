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
	io.parity.image.description="Polkadot: a platform for web3" \
	io.parity.image.source="https://github.com/paritytech/polkadot/blob/${VCS_REF}/docker/Dockerfile" \
	io.parity.image.documentation="https://github.com/paritytech/polkadot/"

RUN useradd -m -u 1000 -U -s /bin/sh -d /substrate substrate && \
	mkdir -p /data /substrate/.local/share/substrate && \
	chown -R substrate:substrate /data && \
	ln -s /data /substrate/.local/share/substrate

COPY --from=builder /substrate/target/$PROFILE/substrate /usr/local/bin
COPY --from=builder /substrate/target/$PROFILE/subkey /usr/local/bin
COPY --from=builder /substrate/target/$PROFILE/node-rpc-client /usr/local/bin
COPY --from=builder /substrate/target/$PROFILE/node-template /usr/local/bin
COPY --from=builder /substrate/target/$PROFILE/chain-spec-builder /usr/local/bin

# checks
RUN ldd /usr/local/bin/substrate && \
	/usr/local/bin/substrate --version

# RUN	rm -rf /usr/bin /usr/sbin

USER substrate
EXPOSE 30333 9933 9944 9615
VOLUME ["/data"]

CMD ["/usr/local/bin/substrate"]
