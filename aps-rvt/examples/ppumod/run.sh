#!/bin/sh

function runfolder() {
    [ -f $1/args.txt ] || (echo "no $1/args.txt"; exit 1)

    
}
