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

import edu.kit.iti.formal.automation.parser.IEC61131Parser;
import edu.kit.iti.formal.automation.st.ast.*;
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
     * @param top a {@link edu.kit.iti.formal.automation.st.ast.Top} object.
     * @param first a {@link org.antlr.v4.runtime.Token} object.
     */
    public static void setPosition(Top top, Token first) {
        top.setStartPosition(new Top.Position(first.getLine(),
                first.getCharPositionInLine()));
    }

    /**
     * <p>setPosition.</p>
     *
     * @param top a {@link edu.kit.iti.formal.automation.st.ast.Top} object.
     * @param first a {@link edu.kit.iti.formal.automation.st.ast.Top} object.
     * @param last a {@link edu.kit.iti.formal.automation.st.ast.Top} object.
     */
    public static void setPosition(Top top, Top first, Top last) {
        top.setStartPosition(first.getStartPosition());
        top.setEndPosition(last.getEndPosition());
    }

    /**
     * <p>setPosition.</p>
     *
     * @param top a {@link edu.kit.iti.formal.automation.st.ast.Top} object.
     * @param first a {@link org.antlr.v4.runtime.Token} object.
     * @param last a {@link edu.kit.iti.formal.automation.st.ast.Top} object.
     */
    public static void setPosition(Top top, Token first, Top last) {
        Utils.setPosition(top, first);
        top.setEndPosition(last.getEndPosition());
    }

    /**
     * <p>setPosition.</p>
     *
     * @param top a {@link edu.kit.iti.formal.automation.st.ast.Top} object.
     * @param ctx a {@link org.antlr.v4.runtime.ParserRuleContext} object.
     */
    public static void setPosition(Top top, ParserRuleContext ctx) {
        setPosition(top, ctx.getStart());
        setLastPosition(top, ctx.getStop());
    }

    /**
     * <p>setPosition.</p>
     *
     * @param top a {@link edu.kit.iti.formal.automation.st.ast.Top} object.
     * @param first a {@link org.antlr.v4.runtime.Token} object.
     * @param last a {@link org.antlr.v4.runtime.Token} object.
     */
    public static void setPosition(Top top, Token first, Token last) {
        setPosition(top, first);
        top.setEndPosition(new Top.Position(last.getLine(),
                last.getCharPositionInLine() + last.getText().length()));
    }

    /**
     * <p>setPositionComplete.</p>
     *
     * @param top a {@link edu.kit.iti.formal.automation.st.ast.Top} object.
     * @param token a {@link org.antlr.v4.runtime.Token} object.
     */
    public static void setPositionComplete(Top top, Token token) {
        setPosition(top, token, token);
    }

    /**
     * <p>setLastPosition.</p>
     *
     * @param ast a {@link edu.kit.iti.formal.automation.st.ast.Top} object.
     * @param tok a {@link org.antlr.v4.runtime.Token} object.
     */
    public static void setLastPosition(Top ast, Token tok) {
        if (tok == null) return;
        ast.setEndPosition(new Top.Position(tok.getLine(), tok.getCharPositionInLine()));
    }

    /**
     * <p>setLastPosition.</p>
     *
     * @param ast a {@link edu.kit.iti.formal.automation.st.ast.Top} object.
     * @param ctx a {@link org.antlr.v4.runtime.ParserRuleContext} object.
     */
    public static void setLastPosition(Top ast, ParserRuleContext ctx) {
        setLastPosition(ast, ctx.getStop());

    }

    /**
     * <p>setPosition.</p>
     *
     * @param top a {@link edu.kit.iti.formal.automation.st.ast.Top} object.
     * @param array a {@link org.antlr.v4.runtime.Token} object.
     * @param ctx a {@link org.antlr.v4.runtime.ParserRuleContext} object.
     */
    public static void setPosition(Top top,
                                   Token array,
                                   ParserRuleContext ctx) {
        setPosition(top, array, ctx.getStop());
    }

    /**
     * <p>setLastPosition.</p>
     *
     * @param ast a {@link edu.kit.iti.formal.automation.st.ast.Top} object.
     * @param ast2 a {@link edu.kit.iti.formal.automation.st.ast.Top} object.
     */
    public static void setLastPosition(Top ast, Top ast2) {
        if(ast2==null || ast == null) return;
        ast.setEndPosition(ast2.getEndPosition());
    }

    /**
     * <p>setPosition.</p>
     *
     * @param ast a {@link edu.kit.iti.formal.automation.st.ast.Top} object.
     * @param integer_type_name a {@link org.antlr.v4.runtime.ParserRuleContext} object.
     * @param rparen a {@link org.antlr.v4.runtime.Token} object.
     */
    public static void setPosition(Top ast, ParserRuleContext integer_type_name, Token rparen) {
    }
}
