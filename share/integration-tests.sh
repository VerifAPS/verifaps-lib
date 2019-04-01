BIN=`pwd`/ide/build/install/ide/bin/
TESTS=`pwd`/share/integration-tests/

if [ ! -d $BIN ]; then
    BIN=$(readlink -f ../ide/build/install/ide/bin/)
    TESTS=$(readlink -f ./integration-tests/)
fi

if [ ! -d $BIN ]; then
    echo "Could not find binary folder: $BIN"
    exit 1
fi



export PATH=$PATH:$BIN
BATS=$(readlink -f $TESTS/../bats-core-1.1.0/bin/bats)


echo $BIN
echo $TESTS
echo $BATS

#############################################################################
## run tests


(cd $TESTS/../..; # always run in root
 $BATS -r  ${TESTS}/)
