#!/bin/sh -x

set -e

(cd ../../../;
 gradle exec:installDist)

XML2ST=../../../exec/build/install/exec/bin/xml2st
XML2ST_ARGS=--translate-sfc

for i in */*.xml; do
    out=${i/xml/st}
    $XML2ST $XML2ST_ARGS \
            -o $out \
            $i
done
