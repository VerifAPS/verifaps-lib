IEC-Run
====

High-Level logical definition
----

IEC-Run will take ST-Code and a list containing variable-assignments for input variables (as used in ST in Program-Declarations) and
return a list containing variable-assignments. Each item in the list represents one cycle of sps-execution.

```kotlin
typealias Identifier = String

class IecRunFascade {
 fun evaluateCode(inputVariableValuesPerCycle: List<Map<Identifier, Value>>) 
    : List<Map<Identifier, Value>>
}
```

Implementation Details
---
 see Module.md