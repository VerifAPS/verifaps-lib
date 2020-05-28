#!/bin/sh -x

set -e

(cd ../../../;
 gradle exec:installDist)

XML2ST=../../../exec/build/install/exec/bin/xml2st
XML2ST_ARGS="--translate-sfc --simplify --ppu"

if [ -z $@ ]; then
    for i in */*.xml; do
        out=${i/xml/st}
        $XML2ST $XML2ST_ARGS \
                -o $out \
                $i
    done
else
    for i in $1/*.xml; do
        out=${i/xml/st}
        $XML2ST $XML2ST_ARGS \
                -o $out \
                $i
    done
fi

