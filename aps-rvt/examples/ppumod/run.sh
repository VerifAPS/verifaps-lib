#!/bin/sh

set -e

(cd ../../../;
 gradle exec:installDist --parallel)


MOD=$(readlink -f ../../../exec/build/install/exec/bin/mod)
MOD_ARGS=@args.txt
TIMELOG=$(pwd)/time.$HOST.txt

rm -f $TIMELOG

if [ -z $@ ]; then 
    for i in */; do
        echo $i
        (cd $i;
         /usr/bin/time -a -o $TIMELOG -f "$i,$E,%S,%U,%P,%W,%w" \
                       $MOD $MOD_ARGS 2>&1 | tee log.txt)
    done
else
    echo "Run... $1"
    (cd $1;
     cat args.txt;
     /usr/bin/time -a -o $TIMELOG -f "$i,$E,%S,%U,%P,%W,%w" \
                   $MOD $MOD_ARGS 2>&1 | tee log.txt)
fi
