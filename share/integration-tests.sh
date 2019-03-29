#!/bin/sh -x
BIN=`pwd`/ide/build/distributions/ide/bin/

if [ ! -f $BIN ]; then
    echo "Could not find binary folder: $BIN"
    exit 1
fi

PATH=$PATH:$BIN

function _run() {
    p=$(pwd)
    $0
    cd $p
}

function geteta_help() {
    geteta.sh --help
}

function geteta_constant_program() {
    cd geteta/examples/constantprogram
    geteta.sh --code constantprogram.st --table constantprogram.tt.txt
}




#############################################################################
## run tests

_run geteta_help

_run geteta_constant_program