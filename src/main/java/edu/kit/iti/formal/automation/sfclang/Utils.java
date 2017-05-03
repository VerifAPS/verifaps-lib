package edu.kit.iti.formal.automation.sfclang;

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

import edu.kit.iti.formal.automation.datatypes.values.PointerValue;
import edu.kit.iti.formal.automation.st.ast.Position;
import edu.kit.iti.formal.automation.st.ast.Top;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.Token;

/**
 * <p>Utils class.</p>
 *
 * @author weigl
 * @version $Id: $Id
 */
public class Utils {
    /**
     * <p>getRandomName.</p>
     *
     * @return a {@link java.lang.String} object.
     */
    public static String getRandomName() {
        return "action_" + (int) (Math.random() * 10000);
    }

    /**
     * <p>setPosition.</p>
     *
     * @param top   a {@link edu.kit.iti.formal.automation.st.ast.Top} object.
     * @param first a {@link org.antlr.v4.runtime.Token} object.
     */
    public static void setStartPosition(Top top, Token first) {
        if (first == null)
            return;
        top.setStartPosition(new Position(first.getLine(),
                first.getCharPositionInLine()));
    }

    public static void setStartPosition(Top top, ParserRuleContext rule) {
        setStartPosition(top, rule.getStart());
    }

    public static void setStartPosition(Top top, Top rule) {
        top.setStartPosition(rule.getStartPosition());
    }

    //
    public static void setLastPosition(Top ast, Token tok) {
        if (tok == null) return;
        ast.setEndPosition(
                new Position(tok.getLine(), tok.getCharPositionInLine()));
    }

    public static void setLastPosition(Top ast, ParserRuleContext ctx) {
        setLastPosition(ast, ctx.getStop());
    }

    public static void setLastPosition(Top ast, Top ast2) {
        if (ast2 == null || ast == null)
            return;
        ast.setEndPosition(ast2.getEndPosition());
    }

    public static void setPosition(Top top, Token first, Token last) {
        setStartPosition(top, first);
        setLastPosition(top, last);
    }

    public static void setPosition(Top top, Top first, Top last) {
        setStartPosition(top, first);
        setLastPosition(top, last);
    }

    public static void setPosition(Top top, Token first, Top last) {
        setStartPosition(top, first);
        setLastPosition(top, last);
    }

    public static void setPosition(Top top, Top first, Token last) {
        setStartPosition(top, first);
        setLastPosition(top, last);
    }

    public static void setPosition(Top top, ParserRuleContext ctx) {
        setStartPosition(top, ctx);
        setLastPosition(top, ctx);
    }

    public static void setPosition(Top top, ParserRuleContext first,
            ParserRuleContext last) {
        setStartPosition(top, first);
        setLastPosition(top, last);
    }

    public static void setPosition(Top top, Token token) {
        setPosition(top, token, token);
    }


    public static void setPosition(Top top,
                                   Token array,
                                   ParserRuleContext ctx) {
        setPosition(top, array, ctx.getStop());
    }

    public static void setPosition(Top ast, ParserRuleContext rule,
            Token stop) {
        setPosition(ast, rule.getStart(), stop);
    }

    public static void setPosition(PointerValue target, PointerValue from) {
        target.setStartPosition(from.getStartPosition().clone());
        target.setEndPosition(from.getEndPosition().clone());
    }
}
