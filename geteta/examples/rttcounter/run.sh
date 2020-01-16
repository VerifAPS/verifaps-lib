#!/usr/bin/env bash

cur=$(pwd)
pushd ../../..
gradle :ide:installDist --parallel
root=$(pwd)
popd

export LANG=C
$root/ide/build/install/ide/bin/reteta \
  --print-augmented-programs\
  --nuxmv ~/share/nuXmv-1.1.1-Linux/bin/nuXmv\
  -t table.tt.txt -P OneCnt.st -P TwoCnt.st