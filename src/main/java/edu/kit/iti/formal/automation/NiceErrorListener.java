package edu.kit.iti.formal.automation;

/*-
 * #%L
 * jpox
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

import com.google.common.base.Strings;
import org.antlr.v4.runtime.*;

/**
 * Created by weigl on 10/07/14.
 */
public class NiceErrorListener extends BaseErrorListener {

	private String content;

	public NiceErrorListener(String content) {
		this.content = content;
	}

	@Override
	public void syntaxError(Recognizer<?, ?> recognizer, Object offendingSymbol, int line, int charPositionInLine,
			String msg, RecognitionException e) {

		String lines[] = content.split("\n");
		System.err.println(line + "@"+charPositionInLine);
		System.err.println(((Parser) recognizer).getRuleInvocationStack());

		RuleContext cur = e.getCtx();
		Parser p = (Parser) recognizer;
		while (cur != null) {
			System.err.println(cur.depth() + " >> " + recognizer.getRuleNames()[cur.getRuleIndex()] + " : "
					+ cur.getText());
			cur = cur.parent;
		}

		System.err.format("ERROR: line %d:%d: %s%n", line, charPositionInLine, msg);
		for (int i = Math.max(0, line - 2); i < lines.length; i++) {
			System.err.println(lines[i]);

			if (i + 1 == line) {
				System.err.println(">" + Strings.repeat(" ", Math.max(0, charPositionInLine - 1)) + "^ " + msg);

				break;

			}
		}
		System.err.format("==============================\n");
	}
}
