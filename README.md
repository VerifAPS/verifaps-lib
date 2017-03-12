# Structured Text Verification Studio - STVS

![Application Screenshot](screenshot.png)

## About

A graphical frontend for the verification of Structured Text code using generalized test tables (see [GeTeTa](getetalink)). This frontend also eases the understanding of test tables via a timing-diagram that shows a concrete example of a general test table.

## How to build and run

System requirements:
 * git
 * [gradle](https://gradle.org/)
 * [nuXmv](https://nuxmv.fbk.eu/)
 * [GeTeTa](getetalink)
 * [Z3](https://github.com/Z3Prover/z3)

First, clone the newest version from master:
```sh
$ git clone https://git.scc.kit.edu/peese/stverificationstudio.git
Username for 'https://git.scc.kit.edu': [your SCC user name]
Password for 'https://ulerr@git.scc.kit.edu': [your SCC password]
$ cd stverificationstudio
```

Then the project can be built and run using gradle:
```sh
$ gradle build
$ gradle run
```

This application does not know where to find the GeTeTa, z3 or nuXmv yet, though, so that has to be configured.

To do that, go to ```Edit``` > ```Preferences``` and change the paths to fit your system. For example:
 * Path to NuXmv Executable: ```/usr/bin/nuXmv```
 * Path to Z3: ```/usr/bin/z3```
 * GeTeTa Command: ```java -jar /opt/share/geteta/geteta.jar -c ${code} -t ${spec} -x```

For running all tests use
```sh
$ gradle test
```

[getetalink]: https://github.com/VerifAPS/geteta
