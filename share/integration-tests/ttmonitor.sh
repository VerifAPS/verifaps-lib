#!/usr/bin/env bash

function ttmonitor_help() {
  ttmonitor --help
}

function xxx_ttmonitor_test_all() {
  cd geteta/examples/
  #tables=$(find -iname '*tt')
  #ttmonitor $tables
}

EXPORTED_TESTS=$(gettests ttmonitor_)
