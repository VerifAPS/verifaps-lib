package edu.kit.iti.formal.automation.run

import edu.kit.iti.formal.automation.datatypes.RecordType
import edu.kit.iti.formal.automation.datatypes.values.Value

class StructValue(dataType: RecordType, value: Map<String, ExpressionValue>) : Value<RecordType, Map<String, ExpressionValue>>(dataType, value) {
}