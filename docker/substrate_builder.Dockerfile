# This is the build stage for Substrate. Here we create the binary.
FROM docker.io/paritytech/ci-linux:production as builder

WORKDIR /substrate
COPY . /substrate
RUN cargo build --locked --release
COPY ./.maintain/init.sh /substrate
RUN ls -al /substrate && ls -al /substrate/.maintain

# This is the 2nd stage: a very small image where we copy the Substrate binary."
FROM docker.io/library/ubuntu:20.04
LABEL description="Multistage Docker image for Substrate: a platform for web3" \
	io.parity.image.type="builder" \
	io.parity.image.authors="chevdor@gmail.com, devops-team@parity.io" \
	io.parity.image.vendor="Parity Technologies" \
	io.parity.image.description="Substrate is a next-generation framework for blockchain innovation 🚀" \
	io.parity.image.source="https://github.com/paritytech/polkadot/blob/${VCS_REF}/docker/substrate_builder.Dockerfile" \
	io.parity.image.documentation="https://github.com/paritytech/polkadot/"

# override interactive installation 
ENV DEBIAN_FRONTEND=noninteractive

COPY --from=builder /substrate/target/release/substrate /usr/local/bin
COPY --from=builder /substrate/target/release/subkey /usr/local/bin
COPY --from=builder /substrate/target/release/node-template /usr/local/bin
COPY --from=builder /substrate/target/release/chain-spec-builder /usr/local/bin
COPY --from=builder /substrate/.maintain/init.sh /tmp
COPY --from=builder /substrate/init.sh /tmp
COPY --from=builder /usr/local/cargo/bin/cargo /usr/local/bin
COPY --from=builder /usr/local/cargo/bin/rustc /usr/local/bin
COPY --from=builder /usr/local/cargo/bin/rustup /usr/local/bin

RUN useradd -m -u 1000 -U -s /bin/sh -d /substrate substrate && \
	mkdir -p /data /substrate/.local/share/substrate && \
	chown -R substrate:substrate /data && \
	ln -s /data /substrate/.local/share/substrate && \
# Sanity checks
	ldd /usr/local/bin/substrate && \
# update rustup to avoid errors verifying ssl issuer certificates
	ls -al /tmp && \
	ls -al /var && \
# move duplicate openssl installation conflicting with with /usr/bin/openssl
	#rm /usr/local/bin/openssl && \
	# find / -name openssl && \
	apt-get update -y && \
	apt-get upgrade -y && \
	apt-get install -y apt-utils curl ca-certificates && \
	update-ca-certificates && \
	# install linker program to join compiled outputs into one file
	# apt-get install -y build-essential && \
	# https://docs.substrate.io/install/linux/
	apt-get install -y clang cmake gcc git libclang-dev libssl-dev \
		libudev-dev llvm make pkg-config protobuf-compiler && \
	# curl https://sh.rustup.rs -sSf | sh -s -- -y && \
	curl --proto '=https' --tlsv1.3 https://sh.rustup.rs -sSf | sh -s -- -y && \
	. $HOME/.cargo/env && \
	chown -R substrate:substrate $HOME/.cargo && \
	rustup update && \
	rustup default stable && \
	rustc --version && \
	#export PATH=$HOME/.cargo/bin:$PATH && \
	# minimize attack surface by removing $HOME/.cargo/bin from PATH
	# mv $HOME/.cargo/bin/cargo /usr/local/bin && \
	# mv $HOME/.cargo/bin/rustc /usr/local/bin && \
	# mv $HOME/.cargo/bin/rustup /usr/local/bin && \
	# move files against conventions to minimize attack surface
	# mv /usr/bin/clang /usr/bin/cmake /usr/bin/gcc /usr/bin/git \
		# /usr/bin/make /usr/bin/pkg-config /usr/local/bin && \
	# mkdir -p /tmp/usr/bin
	# mv /usr/bin/clang /usr/bin/cmake /usr/bin/gcc /usr/bin/git \
	# 	/usr/bin/make /usr/bin/pkg-config /tmp/usr/bin && \
    #. ./tmp/init.sh && \
# overwrite default PATH
	# export CARGO_HOME=$HOME/.cargo
	# export RUSTUP_HOME=$CARGO_HOME/bin
	echo "CARGO_HOME=\$HOME/.cargo" >> $HOME/.bashrc && \
	echo "RUSTUP_HOME=\$CARGO_HOME/bin" >> $HOME/.bashrc && \
	echo "export PATH=\"PATH:$HOME/.cargo/bin:/usr/local/sbin:/usr/local/bin:/usr/bin:/usr/sbin:/sbin:/bin:\$PATH\"" >> $HOME/.bashrc && \
	# . $HOME/.bashrc
	cat $HOME/.bashrc && \
	echo $PATH && \
	# export PATH=$HOME/.cargo/bin:/usr/local/sbin:/usr/local/bin:/sbin:/bin:$PATH && \
# unclutter and minimize the attack surface
	# rm -rf /usr/bin /usr/sbin && \
	# rm -rf /usr/sbin && \
	# find /usr/bin \
	# 	-not -name clang \
	# 	-not -name cmake \
	# 	-not -name gcc \
	# 	-not -name git \
	# 	-not -name make \
	# 	-not -name pkg-config \
	# 	-type f -delete && \
	/usr/local/bin/substrate --version

USER substrate
EXPOSE 30333 9933 9944 9615
VOLUME ["/data"]
