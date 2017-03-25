![STVS Logo](src/main/resources/edu/kit/iti/formal/stvs/logo.png)

Structured Text Verification Studio - STVS
==========================================

![Application Screenshot](screenshot.png)

About
-----

A graphical frontend for the verification of Structured Text code using generalized test tables (see [GeTeTa](https://github.com/VerifAPS/geteta)). This frontend also eases the understanding of test tables via a timing-diagram that shows a concrete example of a general test table.

Installation
------------

Make sure the following programs are installed:
 * [nuXmv](https://nuxmv.fbk.eu/)
 * [GeTeTa](https://github.com/VerifAPS/geteta)
 * [Z3](https://github.com/Z3Prover/z3)
 * [Java](http://www.oracle.com/technetwork/indexes/downloads/index.html#java)

[Download](
https://circleci-tkn.rhcloud.com/api/v1/project/VerifAPS/stvs/tree/circleci-yml/latest/artifacts/stverificationstudio.jar)
 the zip file, unpack it and run the jar named `stvs/stverificationstudio.jar`

Next go to ```Edit``` > ```Preferences``` and change the paths to fit your system. For example:
 * Path to NuXmv Executable: ```/usr/bin/nuXmv```
 * Path to Z3: ```/usr/bin/z3```
 * GeTeTa Command: ```java -jar /opt/share/geteta/geteta.jar -c ${code} -t ${spec} -x```

Contributing
------------

for more information about contributing and compiling from source check out the [contribute guide](CONTRIBUTING.md)
