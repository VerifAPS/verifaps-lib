package edu.kit.iti.formal.automation.st.ast;

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

import edu.kit.iti.formal.automation.VariableScope;
import edu.kit.iti.formal.automation.datatypes.AnyInt;
import edu.kit.iti.formal.automation.datatypes.IECString;
import edu.kit.iti.formal.automation.datatypes.values.ScalarValue;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.Token;

import java.util.Arrays;
import java.util.EmptyStackException;
import java.util.List;
import java.util.Stack;

/**
 * Created by weigl on 24.11.16.
 *
 * @author weigl
 * @version $Id: $Id
 */
public class VariableBuilder {
    private final VariableScope scope;
    private Stack<Integer> stack = new Stack<>();
    private Initialization initialization;
    private List<String> identifiers;
    private TypeDeclaration type;
    private Top.Position pEnd, pStart;

    /**
     * <p>Constructor for VariableBuilder.</p>
     *
     * @param scope a {@link edu.kit.iti.formal.automation.VariableScope} object.
     */
    public VariableBuilder(VariableScope scope) {
        this.scope = scope;
    }

    //region Handling of special flags (like constant, input or global)
    /**
     * <p>clear.</p>
     *
     * @return a {@link edu.kit.iti.formal.automation.st.ast.VariableBuilder} object.
     */
    public VariableBuilder clear() {
        identifiers = null;
        return this;
    }

    /**
     * <p>pop.</p>
     *
     * @return a {@link edu.kit.iti.formal.automation.st.ast.VariableBuilder} object.
     */
    public VariableBuilder pop() {
        stack.pop();
        return this;
    }

    /**
     * <p>peek.</p>
     *
     * @return a int.
     */
    public int peek() {
        try {
            return stack.peek();
        } catch (EmptyStackException e) {
            return 0;
        }
    }

    /**
     * <p>push.</p>
     *
     * @param input a int.
     * @return a {@link edu.kit.iti.formal.automation.st.ast.VariableBuilder} object.
     */
    public VariableBuilder push(int input) {
        stack.push(input);
        return this;
    }

    /**
     * <p>clear.</p>
     *
     * @param i a int.
     * @return a {@link edu.kit.iti.formal.automation.st.ast.VariableBuilder} object.
     */
    public VariableBuilder clear(int i) {
        stack.clear();
        stack.push(i);
        return this;
    }

    /**
     * <p>mix.</p>
     *
     * @param i a int.
     * @return a {@link edu.kit.iti.formal.automation.st.ast.VariableBuilder} object.
     */
    public VariableBuilder mix(int i) {
        push(stack.pop() | i);
        return this;
    }
    //endregion

    /**
     * <p>boolType.</p>
     *
     * @return a {@link edu.kit.iti.formal.automation.st.ast.VariableBuilder} object.
     */
    public VariableBuilder boolType() {
        return type("BOOL");
    }

    /**
     * <p>pointerType.</p>
     *
     * @param pointsTo a {@link java.lang.String} object.
     * @return a {@link edu.kit.iti.formal.automation.st.ast.VariableBuilder} object.
     */
    public VariableBuilder pointerType(String pointsTo) {
        return type(new PointerTypeDeclaration(pointsTo));
    }

    /**
     * <p>stringType.</p>
     *
     * @param base a {@link java.lang.String} object.
     * @param length a {@link edu.kit.iti.formal.automation.datatypes.values.ScalarValue} object.
     * @param def a {@link edu.kit.iti.formal.automation.datatypes.values.ScalarValue} object.
     * @return a {@link edu.kit.iti.formal.automation.st.ast.VariableBuilder} object.
     */
    public VariableBuilder stringType(String base,
                                      ScalarValue<? extends AnyInt, Long> length,
                                      ScalarValue<? extends IECString, String> def) {
        StringTypeDeclaration std = new StringTypeDeclaration();
        std.setBaseTypeName(base);
        std.setSize(length);
        std.setInitialization(def);
        return type(std);
    }


    /**
     * <p>setBaseType.</p>
     *
     * @param baseType a {@link java.lang.String} object.
     * @return a {@link edu.kit.iti.formal.automation.st.ast.VariableBuilder} object.
     */
    public VariableBuilder setBaseType(String baseType) {
        return type(baseType);
    }

    private VariableBuilder type(String baseType) {
        SimpleTypeDeclaration td = new SimpleTypeDeclaration();
        td.setBaseTypeName(baseType);
        return type(td);
    }


    /**
     * <p>type.</p>
     *
     * @param type a {@link edu.kit.iti.formal.automation.st.ast.TypeDeclaration} object.
     * @return a {@link edu.kit.iti.formal.automation.st.ast.VariableBuilder} object.
     */
    public VariableBuilder type(TypeDeclaration type) {
        this.type = type;
        return this;
    }

    /**
     * <p>Setter for the field <code>initialization</code>.</p>
     *
     * @param initialization a {@link edu.kit.iti.formal.automation.st.ast.Initialization} object.
     * @return a {@link edu.kit.iti.formal.automation.st.ast.VariableBuilder} object.
     */
    public VariableBuilder setInitialization(Initialization initialization) {
        this.initialization = initialization;
        return this;
    }

    /**
     * <p>create.</p>
     *
     * @return a {@link edu.kit.iti.formal.automation.st.ast.VariableBuilder} object.
     */
    public VariableBuilder create() {
        for (String id : identifiers) {
            VariableDeclaration vd = new VariableDeclaration(id, peek(), type);
            this.scope.add(vd);
        }
        return this;
    }

    /**
     * <p>close.</p>
     *
     * @return a {@link edu.kit.iti.formal.automation.st.ast.VariableBuilder} object.
     */
    public VariableBuilder close() {
        return create().clear();
    }

    /**
     * <p>identifiers.</p>
     *
     * @param ast a {@link java.util.List} object.
     * @return a {@link edu.kit.iti.formal.automation.st.ast.VariableBuilder} object.
     */
    public VariableBuilder identifiers(List<String> ast) {
        identifiers = ast;
        return this;
    }

    /**
     * <p>setPosition.</p>
     *
     * @param start a {@link org.antlr.v4.runtime.ParserRuleContext} object.
     * @param end a {@link org.antlr.v4.runtime.Token} object.
     */
    public void setPosition(ParserRuleContext start, Token end) {
        setPosition(start.getStart(), end);
    }

    /**
     * <p>setPosition.</p>
     *
     * @param start a {@link org.antlr.v4.runtime.Token} object.
     * @param end a {@link org.antlr.v4.runtime.ParserRuleContext} object.
     */
    public void setPosition(Token start, ParserRuleContext end) {
        setPosition(start, end.getStop());
    }

    /**
     * <p>setPosition.</p>
     *
     * @param start a {@link org.antlr.v4.runtime.Token} object.
     * @param end a {@link org.antlr.v4.runtime.Token} object.
     */
    public void setPosition(Token start, Token end) {
        pStart = new Top.Position(start.getLine(), start.getCharPositionInLine());
        pEnd = new Top.Position(end.getLine(), end.getCharPositionInLine());

    }

    /**
     * <p>identifiers.</p>
     *
     * @param functionName a {@link java.lang.String} object.
     * @return a {@link edu.kit.iti.formal.automation.st.ast.VariableBuilder} object.
     */
    public VariableBuilder identifiers(String... functionName) {
        return identifiers(Arrays.asList(functionName));
    }
}
