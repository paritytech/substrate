#!/bin/bash

set -e

REPO="github.com/paritytech/polkadot-wasm-bin.git"
REPO_AUTH="${GH_TOKEN}:@${REPO}"
SRC="polkadot/runtime/wasm"
DST=".wasm-binaries"
TARGET="wasm32-unknown-unknown"
UTCDATE=`date -u "+%Y%m%d.%H%M%S"`

# NOTE: If script not in root, replace pushd line as below
# pushd $BASEDIR/..
pushd .

echo "*** Building wasm binaries"
cd $SRC
./init.sh || true
./build.sh
cd ../../..

if [ "$TRAVIS_PULL_REQUEST" != "false" -o "$TRAVIS_BRANCH" != "master" ]; then
  popd
  echo "*** Skipping wasm binary publish"
  exit 0
fi

echo "*** Cloning repo"
rm -rf $DST
git clone https://$REPO $DST
cd $DST

echo "*** Setting up GH config"
git config push.default simple
git config merge.ours.driver true
git config user.email "admin@parity.io"
git config user.name "CI Build"
git remote set-url origin https://$REPO_AUTH > /dev/null 2>&1

echo "*** Copying wasm binaries"
rm -rf $TARGET
mkdir -p $TARGET
cp -rf ../$SRC/target/$TARGET/release/*.wasm $TARGET

if [ -f "package.json" ]; then
  echo "*** Updating package.json"
  sed -i '.bak' "s/\"version\": \"[0-9.]*\"/\"version\": \"$UTCDATE\"/g" package.json
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
