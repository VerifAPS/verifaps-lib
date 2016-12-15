package edu.kit.iti.formal.automation.st.util;

import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.util.IllegalFormatFlagsException;

import edu.kit.iti.formal.automation.st.ast.*;

public class ECoreXMLGenerator {

	private Class<? extends Top>[] clazzes;

	@SafeVarargs
	public ECoreXMLGenerator(Class<? extends Top>... clazzes) {
		this.clazzes = clazzes;
	}

	public static void main(String[] args) {
		new ECoreXMLGenerator(Top.class, AssignmentStatement.class, BinaryExpression.class, CaseConditions.class,
				CaseStatement.class, CommentStatement.class, ConfigurationDeclaration.class, Deref.class,
				DirectVariable.class, ExitStatement.class, Expression.class, ExpressionList.class, ForStatement.class,
				FunctionBlockDeclaration.class, FunctionCall.class, FunctionCallStatement.class, GuardedStatement.class,
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
