FROM chevdor/polkadot-base:latest
LABEL maintainer "chevdor@gmail.com"

ARG PROFILE=release

RUN mkdir -p /root/.local/share/Polkadot && \
	ln -s /root/.local/share/Polkadot /data

RUN export PATH=$PATH:$HOME/.cargo/bin && \
	git clone https://github.com/paritytech/polkadot.git && \
	cd polkadot && \
	./build.sh && \
	cargo build --$PROFILE && \
	mv target/$PROFILE/polkadot /usr/local/bin && \
	cargo clean && \
	rm -rf /root/.cargo /root/.rustup /tmp/*

COPY version /polkadot
WORKDIR /polkadot
EXPOSE 30333 9933 9944
VOLUME ["/data"]

CMD ["/bin/sh", "polkadot"]
