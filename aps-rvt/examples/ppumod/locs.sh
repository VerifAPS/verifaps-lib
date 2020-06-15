#!/bin/bash

grep LoC $1 \
    | sed 's/^\[.*\] (INFO) //g' \
    | sed 's/proofEquivalence(.*)://g' \
    | sed 's/\[s.*?\]//g' \
    | sort  \
    | uniq
