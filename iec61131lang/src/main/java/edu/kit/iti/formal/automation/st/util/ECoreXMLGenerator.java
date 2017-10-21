package edu.kit.iti.formal.automation.st.util;

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
 * You should have received a copy of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */

import java.lang.reflect.Field;

import edu.kit.iti.formal.automation.st.ast.*;

/**
 * <p>ECoreXMLGenerator class.</p>
 *
 * @author weigl
 * @version $Id: $Id
 */
public class ECoreXMLGenerator {

	private Class<? extends Top>[] clazzes;

	/**
	 * <p>Constructor for ECoreXMLGenerator.</p>
	 *
	 * @param clazzes a {@link java.lang.Class} object.
	 */
	@SafeVarargs
	public ECoreXMLGenerator(Class<? extends Top>... clazzes) {
		this.clazzes = clazzes;
	}

	/**
	 * <p>main.</p>
	 *
	 * @param args an array of {@link java.lang.String} objects.
	 */
	public static void main(String[] args) {
		new ECoreXMLGenerator(Top.class, AssignmentStatement.class, BinaryExpression.class, CaseCondition.class,
				CaseStatement.class, CommentStatement.class, ConfigurationDeclaration.class, Deref.class,
				DirectVariable.class, ExitStatement.class, Expression.class, ExpressionList.class, ForStatement.class,
				FunctionBlockDeclaration.class, Invocation.class, InvocationStatement.class, GuardedStatement.class,
				Location.class, Reference.class, RepeatStatement.class, ResourceDeclaration.class,
				ReturnStatement.class, Statement.class, SymbolicReference.class, TopLevelScopeElement.class,
				UnaryExpression.class, IfStatement.class, WhileStatement.class).run();
	}

	private void run() {
		for (Class<? extends Top> c : clazzes) {
			System.out.format("<eClassifiers xsi:type=\"ecore:EClass\" name=\"%s\"", c.getSimpleName());
			
			if (c.getSuperclass() != Object.class) {
				System.out.format(" eSuperTypes=\"#//%s\"", c.getSuperclass().getSimpleName());
			}

			// eSuperTypes="#//Guard"
			System.out.println(">");

			for (Field f : c.getDeclaredFields()) {
				Class<?> type = f.getType();
				//System.err.println(f.getType());
				
				if (type == String.class)
					System.out.format(
							"\t<eStructuralFeatures xsi:type=\"ecore:EAttribute\" name=\"%s\" lowerBound=\"1\" "
									+ "eType=\"ecore:EDataType http://www.eclipse.org/emf/2002/Ecore#//EString\" />%n",
							f.getName());
				
				if(type == Boolean.class) {
					System.out.format(
							"\t<eStructuralFeatures xsi:type=\"ecore:EAttribute\" name=\"%s\" lowerBound=\"1\" "
									+ "eType=\"ecore:EDataType http://www.eclipse.org/emf/2002/Ecore#//EBoolean\" />%n",
							f.getName());
				}

				if (type == Integer.class) {
					System.err.println("RROR");
				}

				if (type == Float.class) {
					System.err.println("ERROR");
				}

				if (Top.class.isAssignableFrom(type)){
					System.out.format(
							"\t<eStructuralFeatures xsi:type=\"ecore:EReference\" name=\"%s\" upperBound=\"-1\" eType=\"#//%s\" />%n",
							f.getName(), type.getSimpleName());

				}

			}

			System.out.format("</eClassifiers>%n");
		}

	}

}
