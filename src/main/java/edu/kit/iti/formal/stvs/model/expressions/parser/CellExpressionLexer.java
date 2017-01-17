package edu.kit.iti.formal.stvs.model.expressions.parser;// Generated from /home/philipp/program/PSE/stverificationstudio/antlr/CellExpression.g4 by ANTLR 4.6


import org.antlr.v4.runtime.Lexer;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.Token;
import org.antlr.v4.runtime.TokenStream;
import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.atn.*;
import org.antlr.v4.runtime.dfa.DFA;
import org.antlr.v4.runtime.misc.*;

@SuppressWarnings({"all", "warnings", "unchecked", "unused", "cast"})
public class CellExpressionLexer extends Lexer {
	static { RuntimeMetaData.checkVersion("4.6", RuntimeMetaData.VERSION); }

	protected static final DFA[] _decisionToDFA;
	protected static final PredictionContextCache _sharedContextCache =
		new PredictionContextCache();
	public static final int
		T__0=1, AND=2, ARROW_RIGHT=3, COMMA=4, DIV=5, EQUALS=6, GREATER_EQUALS=7, 
		GREATER_THAN=8, LBRACKET=9, LESS_EQUALS=10, LESS_THAN=11, LPAREN=12, MINUS=13, 
		MOD=14, MULT=15, NOT=16, NOT_EQUALS=17, OR=18, PLUS=19, POWER=20, RBRACKET=21, 
		RPAREN=22, XOR=23, IF=24, FI=25, ELSE=26, GUARD=27, T=28, F=29, IDENTIFIER=30, 
		FLOAT=31, INTEGER=32, WS=33;
	public static String[] modeNames = {
		"DEFAULT_MODE"
	};

	public static final String[] ruleNames = {
		"T__0", "AND", "ARROW_RIGHT", "COMMA", "DIV", "EQUALS", "GREATER_EQUALS", 
		"GREATER_THAN", "LBRACKET", "LESS_EQUALS", "LESS_THAN", "LPAREN", "MINUS", 
		"MOD", "MULT", "NOT", "NOT_EQUALS", "OR", "PLUS", "POWER", "RBRACKET", 
		"RPAREN", "XOR", "IF", "FI", "ELSE", "GUARD", "T", "F", "IDENTIFIER", 
		"DIGIT", "NUMBER", "FLOAT", "INTEGER", "WS"
	};

	private static final String[] _LITERAL_NAMES = {
		null, "'->'", null, "'=>'", "','", "'/'", "'='", "'>='", "'>'", "'['", 
		"'<='", "'<'", "'('", "'-'", null, "'*'", null, null, null, "'+'", "'**'", 
		"']'", "')'", null, "'if'", "'fi'", "'else'", "'::'"
	};
	private static final String[] _SYMBOLIC_NAMES = {
		null, null, "AND", "ARROW_RIGHT", "COMMA", "DIV", "EQUALS", "GREATER_EQUALS", 
		"GREATER_THAN", "LBRACKET", "LESS_EQUALS", "LESS_THAN", "LPAREN", "MINUS", 
		"MOD", "MULT", "NOT", "NOT_EQUALS", "OR", "PLUS", "POWER", "RBRACKET", 
		"RPAREN", "XOR", "IF", "FI", "ELSE", "GUARD", "T", "F", "IDENTIFIER", 
		"FLOAT", "INTEGER", "WS"
	};
	public static final Vocabulary VOCABULARY = new VocabularyImpl(_LITERAL_NAMES, _SYMBOLIC_NAMES);

	/**
	 * @deprecated Use {@link #VOCABULARY} instead.
	 */
	@Deprecated
	public static final String[] tokenNames;
	static {
		tokenNames = new String[_SYMBOLIC_NAMES.length];
		for (int i = 0; i < tokenNames.length; i++) {
			tokenNames[i] = VOCABULARY.getLiteralName(i);
			if (tokenNames[i] == null) {
				tokenNames[i] = VOCABULARY.getSymbolicName(i);
			}

			if (tokenNames[i] == null) {
				tokenNames[i] = "<INVALID>";
			}
		}
	}

	@Override
	@Deprecated
	public String[] getTokenNames() {
		return tokenNames;
	}

	@Override

	public Vocabulary getVocabulary() {
		return VOCABULARY;
	}


	public CellExpressionLexer(CharStream input) {
		super(input);
		_interp = new LexerATNSimulator(this,_ATN,_decisionToDFA,_sharedContextCache);
	}

	@Override
	public String getGrammarFileName() { return "CellExpression.g4"; }

	@Override
	public String[] getRuleNames() { return ruleNames; }

	@Override
	public String getSerializedATN() { return _serializedATN; }

	@Override
	public String[] getModeNames() { return modeNames; }

	@Override
	public ATN getATN() { return _ATN; }

	public static final String _serializedATN =
		"\3\u0430\ud6d1\u8206\uad2d\u4417\uaef1\u8d80\uaadd\2#\u00db\b\1\4\2\t"+
		"\2\4\3\t\3\4\4\t\4\4\5\t\5\4\6\t\6\4\7\t\7\4\b\t\b\4\t\t\t\4\n\t\n\4\13"+
		"\t\13\4\f\t\f\4\r\t\r\4\16\t\16\4\17\t\17\4\20\t\20\4\21\t\21\4\22\t\22"+
		"\4\23\t\23\4\24\t\24\4\25\t\25\4\26\t\26\4\27\t\27\4\30\t\30\4\31\t\31"+
		"\4\32\t\32\4\33\t\33\4\34\t\34\4\35\t\35\4\36\t\36\4\37\t\37\4 \t \4!"+
		"\t!\4\"\t\"\4#\t#\4$\t$\3\2\3\2\3\2\3\3\3\3\3\3\3\3\5\3Q\n\3\3\4\3\4\3"+
		"\4\3\5\3\5\3\6\3\6\3\7\3\7\3\b\3\b\3\b\3\t\3\t\3\n\3\n\3\13\3\13\3\13"+
		"\3\f\3\f\3\r\3\r\3\16\3\16\3\17\3\17\3\17\3\17\5\17p\n\17\3\20\3\20\3"+
		"\21\3\21\3\21\3\21\5\21x\n\21\3\22\3\22\3\22\3\22\5\22~\n\22\3\23\3\23"+
		"\3\23\5\23\u0083\n\23\3\24\3\24\3\25\3\25\3\25\3\26\3\26\3\27\3\27\3\30"+
		"\3\30\3\30\3\30\3\30\3\30\5\30\u0094\n\30\3\31\3\31\3\31\3\32\3\32\3\32"+
		"\3\33\3\33\3\33\3\33\3\33\3\34\3\34\3\34\3\35\3\35\3\35\3\35\3\35\3\35"+
		"\3\35\3\35\5\35\u00ac\n\35\3\36\3\36\3\36\3\36\3\36\3\36\3\36\3\36\3\36"+
		"\3\36\5\36\u00b8\n\36\3\37\3\37\7\37\u00bc\n\37\f\37\16\37\u00bf\13\37"+
		"\3 \3 \3!\6!\u00c4\n!\r!\16!\u00c5\3\"\5\"\u00c9\n\"\3\"\3\"\3\"\5\"\u00ce"+
		"\n\"\3#\5#\u00d1\n#\3#\3#\3$\6$\u00d6\n$\r$\16$\u00d7\3$\3$\2\2%\3\3\5"+
		"\4\7\5\t\6\13\7\r\b\17\t\21\n\23\13\25\f\27\r\31\16\33\17\35\20\37\21"+
		"!\22#\23%\24\'\25)\26+\27-\30/\31\61\32\63\33\65\34\67\359\36;\37= ?\2"+
		"A\2C!E\"G#\3\2\5\5\2C\\aac|\7\2&&\62;C\\aac|\5\2\f\f\17\17\"\"\u00e6\2"+
		"\3\3\2\2\2\2\5\3\2\2\2\2\7\3\2\2\2\2\t\3\2\2\2\2\13\3\2\2\2\2\r\3\2\2"+
		"\2\2\17\3\2\2\2\2\21\3\2\2\2\2\23\3\2\2\2\2\25\3\2\2\2\2\27\3\2\2\2\2"+
		"\31\3\2\2\2\2\33\3\2\2\2\2\35\3\2\2\2\2\37\3\2\2\2\2!\3\2\2\2\2#\3\2\2"+
		"\2\2%\3\2\2\2\2\'\3\2\2\2\2)\3\2\2\2\2+\3\2\2\2\2-\3\2\2\2\2/\3\2\2\2"+
		"\2\61\3\2\2\2\2\63\3\2\2\2\2\65\3\2\2\2\2\67\3\2\2\2\29\3\2\2\2\2;\3\2"+
		"\2\2\2=\3\2\2\2\2C\3\2\2\2\2E\3\2\2\2\2G\3\2\2\2\3I\3\2\2\2\5P\3\2\2\2"+
		"\7R\3\2\2\2\tU\3\2\2\2\13W\3\2\2\2\rY\3\2\2\2\17[\3\2\2\2\21^\3\2\2\2"+
		"\23`\3\2\2\2\25b\3\2\2\2\27e\3\2\2\2\31g\3\2\2\2\33i\3\2\2\2\35o\3\2\2"+
		"\2\37q\3\2\2\2!w\3\2\2\2#}\3\2\2\2%\u0082\3\2\2\2\'\u0084\3\2\2\2)\u0086"+
		"\3\2\2\2+\u0089\3\2\2\2-\u008b\3\2\2\2/\u0093\3\2\2\2\61\u0095\3\2\2\2"+
		"\63\u0098\3\2\2\2\65\u009b\3\2\2\2\67\u00a0\3\2\2\29\u00ab\3\2\2\2;\u00b7"+
		"\3\2\2\2=\u00b9\3\2\2\2?\u00c0\3\2\2\2A\u00c3\3\2\2\2C\u00c8\3\2\2\2E"+
		"\u00d0\3\2\2\2G\u00d5\3\2\2\2IJ\7/\2\2JK\7@\2\2K\4\3\2\2\2LQ\7(\2\2MN"+
		"\7C\2\2NO\7P\2\2OQ\7F\2\2PL\3\2\2\2PM\3\2\2\2Q\6\3\2\2\2RS\7?\2\2ST\7"+
		"@\2\2T\b\3\2\2\2UV\7.\2\2V\n\3\2\2\2WX\7\61\2\2X\f\3\2\2\2YZ\7?\2\2Z\16"+
		"\3\2\2\2[\\\7@\2\2\\]\7?\2\2]\20\3\2\2\2^_\7@\2\2_\22\3\2\2\2`a\7]\2\2"+
		"a\24\3\2\2\2bc\7>\2\2cd\7?\2\2d\26\3\2\2\2ef\7>\2\2f\30\3\2\2\2gh\7*\2"+
		"\2h\32\3\2\2\2ij\7/\2\2j\34\3\2\2\2kp\7\'\2\2lm\7O\2\2mn\7Q\2\2np\7F\2"+
		"\2ok\3\2\2\2ol\3\2\2\2p\36\3\2\2\2qr\7,\2\2r \3\2\2\2sx\7#\2\2tu\7P\2"+
		"\2uv\7Q\2\2vx\7V\2\2ws\3\2\2\2wt\3\2\2\2x\"\3\2\2\2yz\7>\2\2z~\7@\2\2"+
		"{|\7#\2\2|~\7?\2\2}y\3\2\2\2}{\3\2\2\2~$\3\2\2\2\177\u0083\7~\2\2\u0080"+
		"\u0081\7Q\2\2\u0081\u0083\7T\2\2\u0082\177\3\2\2\2\u0082\u0080\3\2\2\2"+
		"\u0083&\3\2\2\2\u0084\u0085\7-\2\2\u0085(\3\2\2\2\u0086\u0087\7,\2\2\u0087"+
		"\u0088\7,\2\2\u0088*\3\2\2\2\u0089\u008a\7_\2\2\u008a,\3\2\2\2\u008b\u008c"+
		"\7+\2\2\u008c.\3\2\2\2\u008d\u008e\7Z\2\2\u008e\u008f\7Q\2\2\u008f\u0094"+
		"\7T\2\2\u0090\u0091\7z\2\2\u0091\u0092\7q\2\2\u0092\u0094\7t\2\2\u0093"+
		"\u008d\3\2\2\2\u0093\u0090\3\2\2\2\u0094\60\3\2\2\2\u0095\u0096\7k\2\2"+
		"\u0096\u0097\7h\2\2\u0097\62\3\2\2\2\u0098\u0099\7h\2\2\u0099\u009a\7"+
		"k\2\2\u009a\64\3\2\2\2\u009b\u009c\7g\2\2\u009c\u009d\7n\2\2\u009d\u009e"+
		"\7u\2\2\u009e\u009f\7g\2\2\u009f\66\3\2\2\2\u00a0\u00a1\7<\2\2\u00a1\u00a2"+
		"\7<\2\2\u00a28\3\2\2\2\u00a3\u00a4\7V\2\2\u00a4\u00a5\7T\2\2\u00a5\u00a6"+
		"\7W\2\2\u00a6\u00ac\7G\2\2\u00a7\u00a8\7v\2\2\u00a8\u00a9\7t\2\2\u00a9"+
		"\u00aa\7w\2\2\u00aa\u00ac\7g\2\2\u00ab\u00a3\3\2\2\2\u00ab\u00a7\3\2\2"+
		"\2\u00ac:\3\2\2\2\u00ad\u00ae\7H\2\2\u00ae\u00af\7C\2\2\u00af\u00b0\7"+
		"N\2\2\u00b0\u00b1\7U\2\2\u00b1\u00b8\7G\2\2\u00b2\u00b3\7h\2\2\u00b3\u00b4"+
		"\7c\2\2\u00b4\u00b5\7n\2\2\u00b5\u00b6\7u\2\2\u00b6\u00b8\7g\2\2\u00b7"+
		"\u00ad\3\2\2\2\u00b7\u00b2\3\2\2\2\u00b8<\3\2\2\2\u00b9\u00bd\t\2\2\2"+
		"\u00ba\u00bc\t\3\2\2\u00bb\u00ba\3\2\2\2\u00bc\u00bf\3\2\2\2\u00bd\u00bb"+
		"\3\2\2\2\u00bd\u00be\3\2\2\2\u00be>\3\2\2\2\u00bf\u00bd\3\2\2\2\u00c0"+
		"\u00c1\4\62;\2\u00c1@\3\2\2\2\u00c2\u00c4\5? \2\u00c3\u00c2\3\2\2\2\u00c4"+
		"\u00c5\3\2\2\2\u00c5\u00c3\3\2\2\2\u00c5\u00c6\3\2\2\2\u00c6B\3\2\2\2"+
		"\u00c7\u00c9\7/\2\2\u00c8\u00c7\3\2\2\2\u00c8\u00c9\3\2\2\2\u00c9\u00ca"+
		"\3\2\2\2\u00ca\u00cb\5A!\2\u00cb\u00cd\7\60\2\2\u00cc\u00ce\5A!\2\u00cd"+
		"\u00cc\3\2\2\2\u00cd\u00ce\3\2\2\2\u00ceD\3\2\2\2\u00cf\u00d1\7/\2\2\u00d0"+
		"\u00cf\3\2\2\2\u00d0\u00d1\3\2\2\2\u00d1\u00d2\3\2\2\2\u00d2\u00d3\5A"+
		"!\2\u00d3F\3\2\2\2\u00d4\u00d6\t\4\2\2\u00d5\u00d4\3\2\2\2\u00d6\u00d7"+
		"\3\2\2\2\u00d7\u00d5\3\2\2\2\u00d7\u00d8\3\2\2\2\u00d8\u00d9\3\2\2\2\u00d9"+
		"\u00da\b$\2\2\u00daH\3\2\2\2\21\2Pow}\u0082\u0093\u00ab\u00b7\u00bd\u00c5"+
		"\u00c8\u00cd\u00d0\u00d7\3\b\2\2";
	public static final ATN _ATN =
		new ATNDeserializer().deserialize(_serializedATN.toCharArray());
	static {
		_decisionToDFA = new DFA[_ATN.getNumberOfDecisions()];
		for (int i = 0; i < _ATN.getNumberOfDecisions(); i++) {
			_decisionToDFA[i] = new DFA(_ATN.getDecisionState(i), i);
		}
	}
}