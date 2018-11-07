FROM frolvlad/alpine-glibc

ARG PROFILE=release

RUN apk add --no-cache build-base \
    cmake \
    linux-headers \
    openssl-dev \
    bash \
    wget && \
    apk add --repository http://nl.alpinelinux.org/alpine/edge/community cargo

# Need nightly cargo for build-deps
WORKDIR /tmp
RUN wget -q https://static.rust-lang.org/dist/2018-11-07/cargo-nightly-x86_64-unknown-linux-gnu.tar.xz
RUN tar xf cargo-nightly-x86_64-unknown-linux-gnu.tar.xz
RUN mv cargo-nightly-x86_64-unknown-linux-gnu/cargo/bin/cargo /usr/bin/cargo
RUN rm -r cargo-nightly-x86_64-unknown-linux-gnu

RUN cargo install cargo-build-deps \
    --git https://github.com/azban/cargo-build-deps \
    --rev 0a83ffef78d559548cba7a30d6dabc83223c5e93

COPY docker/touch_libs.sh /tmp

WORKDIR /substrate
COPY . /substrate
RUN /tmp/touch_libs.sh
RUN cargo build-deps --$PROFILE
