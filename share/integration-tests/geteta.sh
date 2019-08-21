#!/bin/sh

function geteta_help() {
    geteta --help
}

function geteta_w() {
  geteta $@ 2>&1 > /tmp/log.txt
}

function geteta_constantprogram() {
    cd geteta/examples/constantprogram
    geteta -c constantprogram.st --table constantprogram.gtt
}

function geteta_minmax_minimal() {
    cd geteta/examples/MinMax
    geteta -c MinMax.st --table MinMax_Minimal.gtt
}

function geteta_minmax() {
    cd geteta/examples/MinMax
    geteta -c MinMax.st --table MinMax.gtt
}

function geteta_minmax_broken() {
    cd geteta/examples/MinMax
    geteta -c MinMax.st --table MinMax_Broken.gtt
}

function geteta_cexprinter() {
  cd geteta/examples/cycles
  geteta --row-map --cexout -t cycles_wrong.gtt -c cycles.st
}

#EXPORTED_TESTS=(geteta_help geteta_constantprogram geteta_minmax_minimal geteta_minmax geteta_minmax_broken)
EXPORTED_TESTS=$(gettests geteta_)
