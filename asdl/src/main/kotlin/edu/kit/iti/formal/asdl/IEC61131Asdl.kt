@file:JvmName("IEC61131Adsl")

package edu.kit.iti.formal.asdl

import java.io.File

fun main(args: Array<String>) {
    IEC61131Asdl().generate(File(args[0]))
}

class IEC61131Asdl : ADSL() {
    fun generate(output: File) {
        println(output.absoluteFile)
        generate(JavaGenerator(output))
    }

    init {
        module {
            name = "IEC"
            pkgName = "edu.kit.iti.formal.automation.ast"

            group("Top") {
                skip = true
                property("ParserRuleContext? ruleContext")
                property("Position position")

                leaf("VariableDeclaration") {
                    property("String name")
                    property("AnyDt? dataType")
                    property("int flags")
                    property("TypeDeclaration typeDeclaration")
                    property("Scope> parent")
                }

                group("TypeDeclaration") {
                    property("AnyDt? dataType")
                    property("String? typeName")
                    property("String baseTypeName")
                    property("AnyDt baseType")
                    property("Initialization? initialization")

                    leaf("StructureTypeDeclaration") {
                        property("VariableScope fields")
                    }

                    leaf("StringTypeDeclaration") {
                        property("Literal size")
                    }

                    leaf("SimpleTypeDeclaration") {}

                    leaf("PointerTypeDeclaration") {}

                    leaf("EnumerationTypeDeclaration") {
                        property("String* allowedValues")
                        property("Integer* values")
                    }
                    leaf("SubRangeTypeDeclaration") {
                        property("Range range")
                    }

                    leaf("ArrayTypeDeclaration") {
                        property("Range* ranges")
                        property("IECArray type")
                    }
                    leaf("ReferenceSpecification") {
                        property("TypeDeclaration* refTo")
                    }
                }

                group("CaseCondition") {
                    leaf("Range") {
                        property("Literal start")
                        property("Literal stop")
                    }
                    leaf("Enumeration") {
                        property("Literal* literals")
                    }
                }

                group("TopLevelElement") {
                    leaf("TypeDeclarations") {
                        property("TypeDeclaration* declarations")
                    }

                    leaf("TopLevelScopeElement") {
                        property("Scope scope")
                    }
                }

                leaf("Case") {
                    property("Expression conditions")
                    property("StatementList statements")
                }

                leaf("TopLevelElements") {
                    property("TopLevelElement* list")
                }
                leaf("SFCTransition") {
                    property("E* from")
                    property("E* to")
                    property("Expression guard")
                    property("String name")
                    property("int priority")
                }

                leaf("Parameter") {
                    property("String name")
                    property("boolean output")
                    property("Expression expression")
                }

                leaf("SFCImplementation") {
                    property("E* networks")
                    property("E* actions")
                }
                leaf("SFCStep") {
                    property("String name")
                    property("boolean isInitial")
                    property("E* events")
                    property("E* outgoing")
                    property("E* incoming")
                }

                group("Expression") {
                    group("Initialization") {
                        leaf("Literal") {
                            property("T* dataType")
                            property("boolean dataTypeExplicit")
                            property("Token token")
                            property("boolean signed")
                        }
                        leaf("StructureInitialization") {
                            property("K* initValues")
                            property("String structureName")
                        }
                        leaf("PointerValue") {
                        }
                        leaf("Invocation") {
                            property("SymbolicReference callee")
                            property("E* parameters")
                        }
                        leaf("ArrayInitialization") {
                            property("E* initValues")
                        }
                        leaf("IdentifierInitializer") {
                            property("EnumerateType enumType")
                            property("String value")
                        }
                        leaf("ReferenceValue") {
                        }
                    }
                    leaf("Location") {
                        property("E* path")
                    }
                    leaf("UnaryExpression") {
                        property("UnaryOperator operator")
                        property("Expression expression")
                    }
                    leaf("ExpressionList") {
                        property("E* expressions")
                    }
                    leaf("Reference") {
                    }
                    leaf("BinaryExpression") {
                        property("Expression leftExpr")
                        property("Expression rightExpr")
                        property("BinaryOperator operator")
                    }
                }
                group("Statement") {
                    leaf("ExitStatement") {
                        property("ExitStatement EXIT_STATMENT")
                    }
                    leaf("AssignmentStatement") {
                        property("Reference location")
                        property("Expression expression")
                        property("boolean reference")
                        property("boolean assignmentAttempt")
                    }
                    leaf("GuardedStatement") {
                        property("Expression condition")
                        property("StatementList statements")
                    }

                    leaf("InvocationStatement") {
                        property("Invocation invocation")
                    }

                    leaf("ReturnStatement") {}

                    leaf("CaseStatement") {
                        property("Expression expression")
                        property("Case* cases")
                        property("StatementList elseCase")
                    }

                    leaf("ForStatement") {
                        property("String variable")
                        property("Expression start")
                        property("Expression stop")
                        property("Expression step")
                        property("StatementList statements")
                    }
                    leaf("CommentStatement") {
                        property("String comment")
                    }
                    leaf("IfStatement") {
                        property("E* conditionalBranches")
                        property("StatementList elseBranch")
                    }
                }
                leaf("ActionDeclaration") {
                    property("String name")
                    property("StatementList stBody")
                    property("SFCImplementation sfcBody")
                }
                leaf("SFCNetwork") {
                    property("E* steps")
                }
            }
        }
    }
}