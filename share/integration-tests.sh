#!/bin/bash

BIN=$(pwd)/exec/build/install/exec/bin/
TESTS=$(pwd)/share/integration-tests

gettests() {
  set | grep -E "$1.* \(\)" | cut -d' ' -f1 | xargs
}

if [ ! -d $BIN ]; then
    BIN=$(readlink -f ../ide/build/install/ide/bin/)
    TESTS=$(readlink -f ./integration-tests/)
fi

if [ ! -d $BIN ]; then
    echo "Could not find binary folder: $BIN"
    exit 1
fi

if [ -f "$HOME/share/nuXmv-1.1.1-Linux/bin/nuXmv" ];  then
   echo "**add '$HOME/share/nuXmv-1.1.1-Linux/bin/' to path**"
   export PATH=$PATH:"$HOME/share/nuXmv-1.1.1-Linux/bin/"
fi


export NUXMV=nuXmv
export PATH=$PATH:$BIN

echo "**Environment:**"
echo '```'
echo BIN=$BIN
echo TESTS=$TESTS
echo "    $(ls $TESTS/*)"
echo '```'

ROOT=$(readlink -f $TESTS/../..)

function runTest() {
  err=0
  echo "# Run Test: $1"
  startTime=$(date +%s%3N)
  ($1 > $1.log) #set -e?
  err=$?
  endTime=$(date +%s%3N)
  if [ ! $? -eq 0 ]; then
    echo "- Assertion hit!"
    echo "- Output"
    echo '   ```'
    cat $1.log
    echo '   ```'
  else
    echo "- Ok."
  fi
  echo "- Time: $(( $endTime - $startTime)) ms"
  return ${err}
}

declare -a EXPORTED_TESTS

#############################################################################
## run tests

gerror=0
for file in $TESTS/*; do
  echo "Loading Test: $file"
  source $file
  for test in ${EXPORTED_TESTS[@]}; do
     runTest $test
     gerror=$(( $gerror + $? ))
  done
done
exit ${gerror}