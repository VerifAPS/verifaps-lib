#!/usr/bin/env bats

@test "geteta help " {
    geteta --help
}

@test "constant program " {
    (cd geteta/examples/constantprogram;
     geteta -c constantprogram.st --table constantprogram.tt.txt --nuxmv nuXmv)
}
