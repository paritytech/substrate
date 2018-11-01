FROM phusion/baseimage:0.10.1 as builder
LABEL maintainer "chevdor@gmail.com"
LABEL description="This is the build stage for Substrate. Here we create the binary."

ARG PROFILE=release
WORKDIR /substrate

RUN apt-get update && \
	apt-get upgrade -y && \
	apt-get install -y cmake pkg-config libssl-dev git

RUN curl https://sh.rustup.rs -sSf | sh -s -- -y

COPY . /substrate

RUN export PATH=$PATH:$HOME/.cargo/bin && cargo build --$PROFILE

# ===== SECOND STAGE ======

FROM phusion/baseimage:0.10.0
LABEL maintainer "chevdor@gmail.com"
LABEL description="This is the 2nd stage: a very small image where we copy the Substrate binary."
ARG PROFILE=release
COPY --from=builder /substrate/target/$PROFILE/substrate /usr/local/bin

RUN mv /usr/share/ca* /tmp && \
	rm -rf /usr/share/*  && \
	mv /tmp/ca-certificates /usr/share/ && \
	rm -rf /usr/lib/python* && \
	mkdir -p /root/.local/share/Substrate && \
	ln -s /root/.local/share/Substrate /data

RUN	rm -rf /usr/bin /usr/sbin

EXPOSE 30333 9933 9944
VOLUME ["/data"]

CMD ["/usr/local/bin/substrate"]
