FROM rust:latest as builder
LABEL maintainer "chevdor@gmail.com"
LABEL description="This is the build stage for Polkadot. Here we create the binary."

ARG PROFILE=release
WORKDIR /polkadot
COPY . .
RUN cargo build --$PROFILE


FROM ubuntu:latest
LABEL maintainer "chevdor@gmail.com"
LABEL description="This is the 2nd stage: a very small image where we copy the Polkadot binary."
ARG PROFILE=release
COPY --from=builder /polkadot/target/$PROFILE/polkadot /usr/local/bin

RUN apt-get update && \
    apt-get install -y \
    	libssl1.1 && \
    apt-get clean && \
    apt-get autoclean && \
	mkdir -p /root/.local/share/Polkadot && \
	ln -s /root/.local/share/Polkadot /data

EXPOSE 30333 9933 9944
VOLUME ["/data"]

CMD ["/usr/local/bin/polkadot"]
