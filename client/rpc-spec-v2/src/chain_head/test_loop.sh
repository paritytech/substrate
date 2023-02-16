#!/bin/bash


while true
do
    cargo test 2>&1 | tee -a /home/lexnv/workspace/test-log
done
