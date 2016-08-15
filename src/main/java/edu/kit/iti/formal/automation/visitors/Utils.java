package edu.kit.iti.formal.automation.visitors;


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
 */
public class Utils {

	public static ProgramDeclaration findProgram(TopLevelElements tles) {
		for (TopLevelElement t : tles)
			if (t instanceof ProgramDeclaration)
				return (ProgramDeclaration) t;
		return null;
	}

	public static ParseTree parseStructuredText(String input, String rule) {
		return parseStructuredText(new ANTLRInputStream(input), rule);
	}

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
