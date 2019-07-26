IEC-Run
====

High-Level logical definition
----

IEC-Run will take ST-Code and a map of assignments (as used in ST in Program-Declarations) and
return a map of assignments. Each call to `executeCode(topState)` represents one cycle of sps-execution.
You can execute multiple cycles by calling `executeCode`` multiple times, passing in the same `topState`.

Implementation Details
---
 see Module.md