package edu.kit.iti.formal.automation.st.util

/*-
 * #%L
 * iec61131lang
 * %%
 * Copyright (C) 2016 Alexander Weigl
 * %%
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a clone of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */

import edu.kit.iti.formal.automation.st.ast.*

/**
 *
 * ECoreXMLGenerator class.
 *
 * @author weigl
 * @version $Id: $Id
 */
class ECoreXMLGenerator
/**
 *
 * Constructor for ECoreXMLGenerator.
 *
 * @param clazzes a [java.lang.Class] object.
 */
@SafeVarargs
constructor(vararg clazzes: Class<out Top<*>>) {

    private val clazzes: Array<Class<out Top<*>>>

    init {
        this.clazzes = clazzes
    }

    private fun run() {
        for (c in clazzes) {
            System.out.format("<eClassifiers xsi:type=\"ecore:EClass\" name=\"%s\"", c.simpleName)

            if (c.superclass != Any::class.java) {
                System.out.format(" eSuperTypes=\"#//%s\"", c.superclass.simpleName)
            }

            // eSuperTypes="#//Guard"
            println(">")

            for (f in c.declaredFields) {
                val type = f.type
                //System.err.println(f.getType());

                if (type == String::class.java)
                    System.out.format(
                            "\t<eStructuralFeatures xsi:type=\"ecore:EAttribute\" name=\"%s\" lowerBound=\"1\" " + "eType=\"ecore:EDataType http://www.eclipse.org/emf/2002/Ecore#//EString\" />%n",
                            f.name)

                if (type == Boolean::class.java) {
                    System.out.format(
                            "\t<eStructuralFeatures xsi:type=\"ecore:EAttribute\" name=\"%s\" lowerBound=\"1\" " + "eType=\"ecore:EDataType http://www.eclipse.org/emf/2002/Ecore#//EBoolean\" />%n",
                            f.name)
                }

                if (type == Int::class.java) {
                    System.err.println("RROR")
                }

                if (type == Float::class.java) {
                    System.err.println("ERROR")
                }

                if (Top<*>::class.java!!.isAssignableFrom(type)) {
                    System.out.format(
                            "\t<eStructuralFeatures xsi:type=\"ecore:EReference\" name=\"%s\" upperBound=\"-1\" eType=\"#//%s\" />%n",
                            f.name, type.simpleName)

                }

            }

            System.out.format("</eClassifiers>%n")
        }

    }

    companion object {

        /**
         *
         * main.
         *
         * @param args an array of [java.lang.String] objects.
         */
        @JvmStatic
        fun main(args: Array<String>) {
            ECoreXMLGenerator(Top<*>::class.java, AssignmentStatement::class.java, BinaryExpression::class.java, CaseCondition::class.java,
                    CaseStatement::class.java, CommentStatement::class.java, ConfigurationDeclaration::class.java, Deref::class.java,
                    DirectVariable::class.java, ExitStatement::class.java, Expression::class.java, ExpressionList::class.java, ForStatement::class.java,
                    FunctionBlockDeclaration::class.java, Invocation::class.java, InvocationStatement::class.java, GuardedStatement::class.java,
                    Location::class.java, Reference::class.java, RepeatStatement::class.java, ResourceDeclaration::class.java,
                    ReturnStatement::class.java, Statement::class.java, SymbolicReference::class.java, HasScope<*>::class.java,
                    UnaryExpression::class.java, IfStatement::class.java, WhileStatement::class.java).run()
        }
    }

}
