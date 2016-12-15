package edu.kit.iti.formal.automation.sfclang;

import edu.kit.iti.formal.automation.parser.IEC61131Parser;
import edu.kit.iti.formal.automation.st.ast.*;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.Token;

public class Utils {
    public static String getRandomName() {
        return "action_" + (int) (Math.random() * 10000);

    }

    public static void setPosition(Top top, Token first) {
        top.setStartPosition(new Top.Position(first.getLine(),
                first.getCharPositionInLine()));
    }

    public static void setPosition(Top top, Top first, Top last) {
        top.setStartPosition(first.getStartPosition());
        top.setEndPosition(last.getEndPosition());
    }

    public static void setPosition(Top top, Token first, Top last) {
        Utils.setPosition(top, first);
        top.setEndPosition(last.getEndPosition());
    }

    public static void setPosition(Top top, ParserRuleContext ctx) {
        setPosition(top, ctx.getStart());
        setLastPosition(top, ctx.getStop());
    }

    public static void setPosition(Top top, Token first, Token last) {
        setPosition(top, first);
        top.setEndPosition(new Top.Position(last.getLine(),
                last.getCharPositionInLine() + last.getText().length()));
    }

    public static void setPositionComplete(Top top, Token token) {
        setPosition(top, token, token);
    }

    public static void setLastPosition(Top ast, Token tok) {
        if (tok == null) return;
        ast.setEndPosition(new Top.Position(tok.getLine(), tok.getCharPositionInLine()));
    }

    public static void setLastPosition(Top ast, ParserRuleContext ctx) {
        setLastPosition(ast, ctx.getStop());

    }

    public static void setPosition(Top top,
                                   Token array,
                                   ParserRuleContext ctx) {
        setPosition(top, array, ctx.getStop());
    }

    public static void setLastPosition(Top ast, Top ast2) {
        ast.setEndPosition(ast2.getEndPosition());
    }

    public static void setPosition(Top ast, ParserRuleContext integer_type_name, Token rparen) {
    }
}
