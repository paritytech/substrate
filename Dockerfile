# syntax=docker/dockerfile-upstream:experimental

FROM frolvlad/alpine-glibc AS builder
LABEL maintainer="chevdor@gmail.com"
LABEL description="This is the build stage for Substrate. Here we create the binary."

RUN apk add build-base \
    cmake \
    linux-headers \
    openssl-dev && \
    apk add --repository http://nl.alpinelinux.org/alpine/edge/community cargo

WORKDIR /substrate
COPY . /substrate

# Build with mounted cache
ENV CARGO_HOME=/usr/local/cargo
ENV CARGO_TARGET_DIR=/tmp/target
RUN --mount=type=cache,target=/tmp/target \
    --mount=type=cache,target=/usr/local/cargo \
    ["cargo", "build", "--release"]

# Copy binaries into normal layers
RUN --mount=type=cache,target=/tmp/target \
    ["cp", "/tmp/target/release/substrate", "/usr/local/bin/substrate"]

# ===== SECOND STAGE ======

FROM alpine:3.8
LABEL maintainer="chevdor@gmail.com"
LABEL description="This is the 2nd stage: a very small image where we copy the Substrate binary."

COPY --from=builder /usr/local/bin/substrate /usr/local/bin

RUN apk add --no-cache ca-certificates \
    libstdc++ \
    openssl

RUN rm -rf /usr/lib/python* && \
	mkdir -p /root/.local/share/Substrate && \
	ln -s /root/.local/share/Substrate /data

EXPOSE 30333 9933 9944
VOLUME ["/data"]

CMD ["/usr/local/bin/substrate"]
