#!/bin/bash

set -e

REPO="github.com/paritytech/polkadot-wasm-bin.git"
REPO_AUTH="${GH_TOKEN}:@${REPO}"
SRCS=( "polkadot/runtime/wasm" "substrate/executor/wasm" "substrate/test-runtime/wasm" )
DST=".wasm-binaries"
TARGET="wasm32-unknown-unknown"
UTCDATE=`date -u "+%Y%m%d.%H%M%S"`

pushd .

echo "*** Initilising WASM build environment"
cd polkadot/runtime/wasm
./init.sh || true
cd ../../..

for SRC in "${SRCS[@]}"
do
  echo "*** Building wasm binaries in $SRC"
  cd $SRC
  ./build.sh
  cd ../../..
done

if [ "$TRAVIS_PULL_REQUEST" != "false" -o "$TRAVIS_BRANCH" != "master" ]; then
  popd
  echo "*** Skipping wasm binary publish"
  exit 0
fi

echo "*** Cloning repo"
rm -rf $DST
git clone https://$REPO $DST
cd $DST
rm -rf $TARGET
mkdir -p $TARGET

echo "*** Setting up GH config"
git config push.default simple
git config merge.ours.driver true
git config user.email "admin@parity.io"
git config user.name "CI Build"
git remote set-url origin https://$REPO_AUTH > /dev/null 2>&1

for SRC in "${SRCS[@]}"
do
  echo "*** Copying wasm binaries from $SRC"
  cp ../$SRC/target/$TARGET/release/*.wasm $TARGET
done

if [ -f "package.json" ]; then
  echo "*** Updating package.json"
  sed -i -e "s/\"version\": \"[0-9.]*\"/\"version\": \"$UTCDATE\"/g" package.json
  rm -rf package.json.bak
fi

echo "*** Adding to git"
echo "$UTCDATE" > README.md
git add --all .
git commit -m "$UTCDATE"

echo "*** Pushing upstream"
git push --quiet origin HEAD:refs/heads/master > /dev/null 2>&1

echo "*** Cleanup"
cd ..
rm -rf $DST
popd

echo "*** Completed"
exit 0
