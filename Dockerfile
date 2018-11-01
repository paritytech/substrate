FROM frolvlad/alpine-glibc AS builder
LABEL maintainer="chevdor@gmail.com"
LABEL description="This is the build stage for Polkadot. Here we create the binary."

RUN apk add build-base \
    cmake \
    linux-headers \
    openssl-dev && \
    apk add --repository http://nl.alpinelinux.org/alpine/edge/community cargo

ARG PROFILE=release
WORKDIR /polkadot

COPY . /polkadot

RUN cargo build --$PROFILE

# ===== SECOND STAGE ======

FROM alpine:3.8
LABEL maintainer="chevdor@gmail.com"
LABEL description="This is the 2nd stage: a very small image where we copy the Polkadot binary."
ARG PROFILE=release
COPY --from=builder /polkadot/target/$PROFILE/polkadot /usr/local/bin

RUN apk add --no-cache ca-certificates \
    libstdc++ \
    openssl

RUN rm -rf /usr/lib/python* && \
	mkdir -p /root/.local/share/Polkadot && \
	ln -s /root/.local/share/Polkadot /data

EXPOSE 30333 9933 9944
VOLUME ["/data"]

CMD ["/usr/local/bin/polkadot"]
