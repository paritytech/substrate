#!/usr/bin/env bash
set -e

source /root/.cargo/env

spartan-farmer plot 256000 spartan

while ! nc -z node 9944; do
  sleep 1
done

exec spartan-farmer farm --ws-server ws://node:9944
