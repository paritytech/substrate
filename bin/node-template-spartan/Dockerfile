FROM ubuntu:20.04

WORKDIR /code

RUN \
    apt-get update && \
    DEBIAN_FRONTEND=noninteractive apt-get install -y --no-install-recommends \
        ca-certificates \
        curl \
        gcc \
        llvm \
        clang \
        make \
        m4 && \
    curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y --default-toolchain nightly

RUN /root/.cargo/bin/rustup target add wasm32-unknown-unknown

COPY bin /code/bin
COPY client /code/client
COPY frame /code/frame
COPY primitives /code/primitives
COPY test-utils /code/test-utils
COPY utils /code/utils
COPY Cargo.lock /code/Cargo.lock
COPY Cargo.toml /code/Cargo.toml

RUN \
    /root/.cargo/bin/cargo build --bin node-template-spartan --release && \
    mv target/release/node-template-spartan node-template-spartan && \
    rm -rf target

FROM ubuntu:20.04

COPY --from=0 /code/node-template-spartan /node-template-spartan

USER nobody:nogroup

ENTRYPOINT ["/node-template-spartan"]
