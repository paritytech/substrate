FROM debian:stretch-slim
LABEL maintainer "devops-team@parity.io"
LABEL description="Substrate: The platform for blockchain innovators"

RUN apt-get update && \
    DEBIAN_FRONTEND=noninteractive apt-get upgrade -y && \
    DEBIAN_FRONTEND=noninteractive apt-get install -y \
      libssl1.1 \
      ca-certificates \
      curl && \
    apt-get autoremove -y && \
    apt-get clean && \
    find /var/lib/apt/lists/ -type f -not -name lock -delete

COPY ./substrate /usr/local/bin


RUN useradd -m -u 1000 -U -s /bin/sh -d /substrate substrate
USER substrate

ENV RUST_BACKTRACE 1

# check if executable works in this container
RUN /usr/local/bin/substrate --version

EXPOSE 30333 9933 9944
VOLUME ["/substrate"]

ENTRYPOINT ["/usr/local/bin/substrate"]

