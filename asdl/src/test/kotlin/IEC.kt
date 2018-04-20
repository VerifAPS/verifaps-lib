import edu.kit.iti.formal.asdl.ADSL

class IEC : ADSL() {
    init {
        module {
            name = "IEC"
            pkgName = "edu.kit.iti.formal.automation.ast"

            leaf("VariableDeclaration")

            group("Top") {
                group("TypeDeclaration") {
                    leaf("StructureTypeDeclaration")
                    leaf("StringTypeDeclaration")
                    leaf("SimpleTypeDeclaration")
                    leaf("PointerTypeDeclaration")
                    leaf("EnumerationTypeDeclaration")
                    leaf("SubRangeTypeDeclaration")
                    leaf("ArrayTypeDeclaration")
                    leaf("ReferenceSpecification")
                }

                group("CaseCondition") {
                    leaf("Range")
                    leaf("Enumeration")
                    leaf("IntegerCondition")
                }

                leaf("TopLevelElements")

                group("TopLevelElement") {
                    leaf("TypeDeclarations")
                    group("TopLevelScopeElement")
                }

                leaf("Case")
                leaf("SFCTransition")
                leaf("SFCImplementation")
                leaf("SFCStep")
                leaf("SFCNetwork")
                leaf("ActionDeclaration")

                leaf("Parameter")

                group("Expression") {
                    group("Initialization") {
                        group("Literal") {
                            leaf("IntegerLiteral")
                            leaf("StringLiteral")
                            leaf("FloatLiteral")
                            leaf("ArrayLiteral")
                        }
                        leaf("StructureInitialization")
                        leaf("PointerValue")
                        leaf("ArrayInitialization")
                        leaf("IdentifierInitializer")
                        leaf("ReferenceValue")
                    }
                    leaf("Location")
                    leaf("UnaryExpression")
                    //ExpressionList
                    leaf("Reference")
                    leaf("BinaryExpression")
                }

                group("Statement") {
                    leaf("ExitStatement")
                    leaf("AssignmentStatement")
                    leaf("WhileStatement")
                    leaf("RepeatStatement")
                    leaf("InvocationStatement")
                    leaf("ReturnStatement")
                    leaf("CaseStatement")
                    leaf("ForStatement")
                    leaf("CommentStatement")
                    leaf("IfStatement")
                }
            }
        }
    }
}