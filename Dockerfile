FROM phusion/baseimage:0.11 as builder
LABEL maintainer="team@cere.network"
LABEL description="This is the build stage to create the binary."
ARG PROFILE=release
WORKDIR /cerenetwork
COPY . /cerenetwork

# Copy smart-contract artifacts (cere01.wasm and metadata.json)
ARG SMART_CONTRACT_VERSION=1.1.0
FROM cere-enterprise-smart-contracts/smart-contracts:$SMART_CONTRACT_VERSION as smart-contracts
COPY --from=smart-contracts /smart-contracts/artifacts/cere01.wasm /cerenetwork/frame/ddc-metrics-offchain-worker/src/tests/test_data
COPY --from=smart-contracts /smart-contracts/artifacts/metadata.json /cerenetwork/frame/ddc-metrics-offchain-worker/src/tests/test_data

RUN apt-get update && \
	apt-get upgrade -y && \
	apt-get install -y cmake pkg-config libssl-dev git clang
RUN curl https://sh.rustup.rs -sSf | sh -s -- -y && \
    export PATH=$PATH:$HOME/.cargo/bin && \
    scripts/init.sh && \
    cargo +nightly-2021-05-07 build --$PROFILE

# ===== SECOND STAGE ======
FROM phusion/baseimage:0.11
LABEL maintainer="team@cere.network"
LABEL description="This is the optimization to create a small image."
ARG PROFILE=release
COPY --from=builder /cerenetwork/target/$PROFILE/cere /usr/local/bin

RUN mv /usr/share/ca* /tmp && \
	rm -rf /usr/share/*  && \
	mv /tmp/ca-certificates /usr/share/ && \
	rm -rf /usr/lib/python* && \
	useradd -m -u 1000 -U -s /bin/sh -d /cerenetwork cerenetwork && \
	mkdir -p /cerenetwork/.local/share/cerenetwork && \
	mkdir -p /cerenetwork/.local/share/cere && \
	chown -R cerenetwork:cerenetwork /cerenetwork/.local && \
	ln -s /cerenetwork/.local/share/cere /data && \
	rm -rf /usr/bin /usr/sbin

USER cerenetwork
EXPOSE 30333 9933 9944 9615
VOLUME ["/data"]

CMD ["/usr/local/bin/cere"]
