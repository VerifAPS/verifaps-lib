#!/usr/bin/env bash

export NUXMV=~/share/nuXmv-1.1.1-Linux/bin/nuXmv
export LANG=C

cur=$(pwd)

while [[ ! -f ./gradlew ]]; do
  cd ..
done

gradle :exec:installDist --parallel
ROOT=$(pwd)


cd $cur



function reteta() {
  $ROOT/ide/build/install/ide/bin/reteta $@
}

function geteta() {
  $ROOT/ide/build/install/ide/bin/geteta $@
}