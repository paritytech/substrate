#!/bin/sh --
set -eu
case $0 in
   (/*) dir=${0%/*}/;;
   (*/*) dir=./${0%/*};;
   (*) dir=.;;
esac

find "$dir/.." -name Cargo.lock -execdir cargo update \;
