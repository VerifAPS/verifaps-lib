IEC-Run
====

High-Level logical definition
----

IEC-Run will take ST-Code and a map of assignments (as used in ST in Program-Declarations) and
return a map of assignments. Each call to `executeCode(topState)` represents one cycle of sps-execution.
You can execute multiple cycles by calling `executeCode`` multiple times, passing in the same `topState`.

```kotlin
typealias ExpressionValue = Value<out AnyDt, out kotlin.AnyDt>
// TopState has basically this type:
typealias TopState = HashMap<String, Optional<ExpressionValue>>


class IecRunFascade {
 fun evaluateCode(beforeState : TopState) 
    : TopState
 
 fun evaluateCode() : TopState
}
```

Implementation Details
---
 see Module.md