# Module iec-run

Execution of a single Cycle
---

The class `Runtime` will execute statements
 and delegate expression valuation to `ExpressionEvaluator`. `ExpressionEvaluator` can intern create a
 new `Runtime` for function calls etc.
 
Both `Runtime` and `ExpressionEvaluator` operate on the `State` to store the variable assignments.

`ExpressionEvaluator` calls `OperationEvaluator` for evaluating the Operator in concrete values.


```kotlin
ExpressionEvaluator(Expression) :  ExpressionValue
//as compared to
OperationEvaluator(Operator, ExpressionValue, ExpressionValue) : ExpressionValue
```
