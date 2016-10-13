package edu.kit.iti.formal.exteta.io;

import org.antlr.v4.runtime.BaseErrorListener;
import org.antlr.v4.runtime.Recognizer;
import org.antlr.v4.runtime.misc.ParseCancellationException;

public class ThrowingErrorListener extends BaseErrorListener {

	public static final ThrowingErrorListener INSTANCE = new ThrowingErrorListener();

	@Override
	public void syntaxError(Recognizer<?, ?> recognizer, Object offendingSymbol, int line, int charPositionInLine,
			String msg, org.antlr.v4.runtime.RecognitionException e) {
		throw new ParseCancellationException("line " + line + ":" + charPositionInLine + " " + msg);
	}
}