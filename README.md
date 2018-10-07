# verifaps-lib 

Library and programs for the verification of software for automated production systems.

* License: GPLv3
* Homepage: https://formal.iti.kit.edu/verifaps 

## How to build

Create all programs: 

```
$ ./gradlew :casestudies:installDist
```

You can find the programs in `./casestudies/build/install/casestudies/bin`.

Test project:

```
$ ./gradlew check
```

## Project overview

* iec61131-lang -- Parser and AST for StructuredText and Sequential Function Chart.
* geteta -- Framework for generalized Test Tables.
* casestudies -- contains generic programs and programs for specific case studies.
* flycheck  -- interface for syntax and type checking of Structured Text files.
* iec-modularization -- Modularized regression verification.
* iec-run -- Interpreter for Structured Text
* iec-xml -- Loading and Parsing of PCLOpenXML projects.
* smv-model -- Model and parser for SMV. Also includes nuXmv interface.
* web-backend -- Backend for the web frontend. (upcoming)
