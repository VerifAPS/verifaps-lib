package edu.kit.iti.formal.automation.sfclang;

import edu.kit.iti.formal.automation.st.ast.Expression;
import edu.kit.iti.formal.automation.st.ast.Top;
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


    public static void setPosition(Top top, Token first, Token last) {
        setPosition(top, first);
        top.setEndPosition(new Top.Position(last.getLine(),
                last.getCharPositionInLine() + last.getText().length()));
    }

    public static void setPositionComplete(Top top, Token token) {
        setPosition(top, token, token);
    }
}
