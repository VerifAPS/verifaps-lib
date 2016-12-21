package edu.kit.iti.formal.automation.visitors;

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


import edu.kit.iti.formal.automation.parser.IEC61131Lexer;
import edu.kit.iti.formal.automation.parser.IEC61131Parser;
import edu.kit.iti.formal.automation.st.ast.*;
import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.Lexer;
import org.antlr.v4.runtime.Token;
import org.antlr.v4.runtime.tree.ParseTree;

import java.lang.reflect.Method;
import java.util.List;

/**
 * Created by weigla on 09.06.2014.
 *
 * @author weigl
 * @version $Id: $Id
 */
public class Utils {

	/**
	 * <p>findProgram.</p>
	 *
	 * @param tles a {@link edu.kit.iti.formal.automation.st.ast.TopLevelElements} object.
	 * @return a {@link edu.kit.iti.formal.automation.st.ast.ProgramDeclaration} object.
	 */
	public static ProgramDeclaration findProgram(TopLevelElements tles) {
		for (TopLevelElement t : tles)
			if (t instanceof ProgramDeclaration)
				return (ProgramDeclaration) t;
		return null;
	}

	/**
	 * <p>parseStructuredText.</p>
	 *
	 * @param input a {@link java.lang.String} object.
	 * @param rule a {@link java.lang.String} object.
	 * @return a {@link org.antlr.v4.runtime.tree.ParseTree} object.
	 */
	public static ParseTree parseStructuredText(String input, String rule) {
		return parseStructuredText(new ANTLRInputStream(input), rule);
	}

	/**
	 * <p>parseStructuredText.</p>
	 *
	 * @param stream a {@link org.antlr.v4.runtime.ANTLRInputStream} object.
	 * @param rule a {@link java.lang.String} object.
	 * @return a {@link org.antlr.v4.runtime.tree.ParseTree} object.
	 */
	public static ParseTree parseStructuredText(ANTLRInputStream stream, String rule) {
		try {
			IEC61131Lexer stl = new IEC61131Lexer(stream);
			CommonTokenStream cts = new CommonTokenStream(stl);
			IEC61131Parser stp = new IEC61131Parser(cts);
			Class<?> clazz = stp.getClass();
			Method method = null;
			method = clazz.getMethod(rule);
			return (ParseTree) method.invoke(stp);
		} catch (Exception e) {
			return null;
		}
	}

	/**
	 * <p>compareTokens.</p>
	 *
	 * @param tokens a {@link java.util.List} object.
	 * @param expected an array of {@link java.lang.String} objects.
	 * @param lexer a {@link org.antlr.v4.runtime.Lexer} object.
	 */
	public static void compareTokens(List<? extends Token> tokens, String[] expected, Lexer lexer) {
		try {
			for (int i = 0; i < expected.length; i++) {
				int expect = lexer.getTokenType(expected[i]);
				Token tok = tokens.get(i);
				String tokName = IEC61131Lexer.tokenNames[tok.getType()];

				if (!expected[i].contentEquals(tokName)) {
					throw new AssertionError(
							String.format("Token mismatch! Expected: %s but got %s", expected[i], tokName));
				}
			}
		} catch (IndexOutOfBoundsException e) {
			throw new AssertionError("Not enough tokens found!");
		}

		if (expected.length < tokens.size()) {
			throw new AssertionError("Too much tokens found!");
		}
	}

}
