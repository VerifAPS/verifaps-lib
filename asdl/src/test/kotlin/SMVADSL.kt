import edu.kit.iti.formal.asdl.ADSL

/**
 *
 * @author Alexander Weigl
 * @version 1 (15.04.18)
 */
class SMVADSL : ADSL() {
    init {
        module {
            pkgName = "edu.kit.iti.formal.smv.ast"
            classPrefix = "Smv"
            name = "Ast"

            group("Ast") {
                group("Expr") {
                    property("Position position")
                    leaf("Assignment", "Variable rhs, Expr lhs")
                    leaf("BinaryExpression", "Expr left, BinaryOperator op, Expr right")
                    leaf("CaseExpression", "Case* cases")
                    leaf("Function", "String name", "Expr* arguments")
                    group("Literal") {
                        leaf("WordLiteral", "int width, boolean signed, BigInteger value")
                        leaf("IntegerLiteral", "BigInteger value")
                        leaf("RealLiteral", "BigDecimal value")
                        leaf("BoolLiteral", "boolean value")
                        leaf("EnumLiteral", "String value")
                        leaf("EnumLiteral", "String value")
                    }
                    leaf("SQuantified", "Quantifier quantifier, Expr* quantified")
                    leaf("UnaryExpression", "UnaryOperator op, Expr expr")
                    leaf("Variable", "String* names")
                }
                leaf("SMVModule")
            }
        }
    }
}