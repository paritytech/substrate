#!/usr/bin/env bash

export dir_path_to="${1:-./}"
export image_tag="${2:-latest}"
docker pull docker pull cerebellumnetwork/pos-node:"$image_tag"
id=$(docker create "cerebellumnetwork/pos-node:$image_tag")
docker cp "${id}":/home/cere/node-runtime-artifacts "$dir_path_to"
docker rm -v "$id"