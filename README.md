# iec61131lang

[![Build Status](https://travis-ci.org/VerifAPS/iec61131lang.svg?branch=master)](https://travis-ci.org/VerifAPS/iec61131lang)
[![CircleCI](https://circleci.com/gh/VerifAPS/iec61131lang.svg?style=svg)](https://circleci.com/gh/VerifAPS/iec61131lang)

Parser and AST for StructuredText, Sequential Function Charts and Function Blocks.


* Licsense: GPL v3
* Author
  * Alexander Weigl (@wadoon)

# Getting Started


```
$ git clone  https://github.com/VerifAPS/iec61131lang.git
$ mvn compile assembly
$ mvn install
```

# TODO

* [ ] Unit Tests, especially for wrong expressions and statements
* [ ] Error Messages
* [ ] Documentation

# Language Features

* [ ] Structured Text
  * [x] Constrol Structures
    * [x] if-elseif-else
    * [x] case
      * [x] ordinals
      * [x] enumerations
      * [x] range
    * [x] for
    * [x] while
    * [x] repeat-until
  * [x] POUs
    * [x] Function
    * [x] Function Block
    * [x] Program
  * [ ] User-defined Datatypes
    * [x] Enums
    * [x] Ranges
    * [x] Arrays
    * [x] Structs/Records
  * [?] Pointers (need to be tested)
  * [ ] Object Oriented Function Blocks
    * [ ] Interfaces
    * [ ] Extends Clause
* [ ] Sequential Function Chart
  * [x] Steps with Actions
  * [x] Transitions
    * [x] fork/join (divergence/convergence)
    * [x] split/merge (simultanousely divergence/convergence)
    * [x] Guards in Structured Text
  * [ ] Timed (not planned)

# Sequential Function Chart Syntax

This is not a standard language.


## Example:

```
SFC example

    VAR_OUTPUT
        o : bool;
    END_VAR

    STEP A
        on active action
            o := true;
        end_action
    END_STEP

    STEP B
       on active action
            o := false;
       end_action
    END_STEP

    GOTO true :: A -> B
    GOTO true :: B -> A
END_SFC
```

## EBNF

```
<SFC>  :==  SFC <identifier>
                <elements>*
            END_SFC

<element>   :== <var_decl> | <step_decl> | <transition>
<step_decl> :== STEP <identifier>
                  on <event> (action <statement>* end_action
                             | <function-name> )
                END_STEP
<transition> :== GOTO <guard> :: <identifier>* -> <identifier>*
```

`<event>` can be either `active`, `exit` or `entry`. `<statement>` refers to
valid Structured Text statements. `<var_decl>` responses to classical variable
declearation in IEC61131-3.
