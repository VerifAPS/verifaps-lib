#!/bin/bash

cd ..

function d {
	(cd $1 && mvn -DperformRelease=true site:site site:deploy deploy) &
}

d iec61131lang
d parent
d smv-model
d iec-symbex
d geteta 
