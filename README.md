# verifaps-lib  [![CircleCI](https://circleci.com/gh/VerifAPS/verifaps-lib/tree/master.svg?style=svg)](https://circleci.com/gh/VerifAPS/verifaps-lib/tree/master) [![Quality Gate Status](https://sonarcloud.io/api/project_badges/measure?project=VerifAPS_verifaps-lib&metric=alert_status)](https://sonarcloud.io/dashboard?id=VerifAPS_verifaps-lib)
 
Library and programs for the verification of software for automated production systems.

* License: GPLv3
* Homepage: https://formal.iti.kit.edu/verifaps 

## How to build

Create all programs: 

```
$ ./gradlew :exec:installDist
```

You can find the programs in `./exec/build/install/exec/bin`.

Test project:

```
$ ./gradlew check
```

## Modules overview

* `symbex` -- Symbolic execution engine and program transformations for Structured Text
* `aps-rvt` -- (Modular) Regression verification for Structued Text code
* `lang` -- Parser and AST for StructuredText, Sequential Function Chart, and Function Blocks
* `geteta` -- Framework and Tools for Generalized Test Tables
* `exec` -- Top-level module containing for generating programs
* `ide` -- graphical editor for editing Strutured Text and test table files
* `run` -- Interpreter for executing Structured Text
* `xml` -- Loading and Parsing of PCLOpenXML projects
* `smv` -- Model and parser for SMV -- also includes nuXmv interface
* `smt` -- AST and parser for SMT (SExpr)
* `util` and `util-test` -- 
* `web-backend` (disabled) -- Backend for the web frontend. (upcoming)