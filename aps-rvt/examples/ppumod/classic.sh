#!/bin/sh

set -e

(cd ../../../;
 gradle exec:installDist --parallel)

export NUXMV=$HOME/share/nuXmv-1.1.1-Linux/bin/nuXmv

MOD=$(readlink -f ../../../exec/build/install/exec/bin/mod)
MOD_ARGS="@args.txt
  --disable-proof-body-equivalence-smt\
  --disable-proof-body-equivalence-ssa\
  --disable-proof-body-equivalence-source\
  --disable-proof-body-equivalence-with-abstraction-sub-frames\
  --disable-proof-body-equivalence-with-abstraction-body\
  --disable-proof-body-equivalence-with-abstraction\
  --disable-update-cache\
  --disable-check-cache"


TIMELOG=$(pwd)/time.txt

if [ -z $@ ]; then
    for i in */; do
        echo $i
        (cd $i;
         /usr/bin/time -a -o $TIMELOG -f "$i,$E,%S,%U,%P,%W,%w" \
                       $MOD $MOD_ARGS 2>&1 | tee logc.txt)
    done
else
    echo "Run... $1"
    (cd $1;
     cat args.txt;
     /usr/bin/time -a -o $TIMELOG -f "$1,%E,%S,%U,%P,%W,%w" \
                   $MOD $MOD_ARGS 2>&1 | tee logc.txt)
fi
