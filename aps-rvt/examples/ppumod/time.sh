#!/bin/bash

grep Timings $1 \
    | sed 's/^\[.*\] (INFO) //g' \
    | sed 's/proofEquivalence//g' \
    | sort
