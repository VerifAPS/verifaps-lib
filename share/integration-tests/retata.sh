#!/bin/sh

function reteta_help() {
  reteta --help
}

function reteta_rttcounter() {
  cd geteta/examples/rttcounter
  reteta --print-augmented-programs\
    --nuxmv ~/share/nuXmv-1.1.1-Linux/bin/nuXmv\
    -t table.tt.txt -P OneCnt.st -P TwoCnt.st \
    || exit
  cat -n table.tt/*.st
}
EXPORTED_TESTS=(reteta_help)
