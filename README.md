![STVS Logo](src/main/resources/edu/kit/iti/formal/stvs/logo.png)
[![CircleCI](https://circleci.com/gh/VerifAPS/stvs.svg?style=svg)](https://circleci.com/gh/VerifAPS/stvs)
[![Codacy Badge](https://api.codacy.com/project/badge/Grade/ddb6c2defb4b445ebf1f6dc2d6205841)](https://www.codacy.com/app/wadoon/stvs?utm_source=github.com&amp;utm_medium=referral&amp;utm_content=VerifAPS/stvs&amp;utm_campaign=Badge_Grade)

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
https://git.scc.kit.edu/api/v3/projects/1721/builds/artifacts/master/download?job=buildFatJar)
 the zip file, unpack it and run the jar named `stvs/stverificationstudio.jar`

Next go to ```Edit``` > ```Preferences``` and change the paths to fit your system. For example:
 * Path to NuXmv Executable: ```/usr/bin/nuXmv```
 * Path to Z3: ```/usr/bin/z3```
 * GeTeTa Command: ```java -jar /opt/share/geteta/geteta.jar -c ${code} -t ${spec} -x```

Contributing
------------

for more information about contributing and compiling from source check out the [contribute guide](CONTRIBUTING.md)
