package edu.kit.iti.formal.automation.st.ast;

import edu.kit.iti.formal.automation.VariableScope;
import edu.kit.iti.formal.automation.datatypes.AnyInt;
import edu.kit.iti.formal.automation.datatypes.IECString;
import edu.kit.iti.formal.automation.datatypes.values.ScalarValue;
import edu.kit.iti.formal.automation.parser.IEC61131Parser;
import edu.kit.iti.formal.automation.sfclang.Utils;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.Token;

import java.util.EmptyStackException;
import java.util.List;
import java.util.Stack;

/**
 * Created by weigl on 24.11.16.
 */
public class VariableBuilder {
    private final VariableScope scope;
    private Stack<Integer> stack = new Stack<>();
    private Initialization initialization;
    private List<String> identifiers;
    private TypeDeclaration type;
    private Top.Position pEnd, pStart;

    public VariableBuilder(VariableScope scope) {
        this.scope = scope;
    }

    //region Handling of special flags (like constant, input or global)
    public VariableBuilder clear() {
        return clear(0);
    }

    public VariableBuilder pop() {
        stack.pop();
        return this;
    }

    public int peek() {
        try {
            return stack.peek();
        } catch (EmptyStackException e) {
            return 0;
        }
    }

    public void push(int input) {
        stack.push(input);
    }

    public VariableBuilder clear(int i) {
        stack.clear();
        stack.push(i);
        return this;
    }

    public VariableBuilder mix(int i) {
        push(stack.pop() | i);
        return this;
    }
    //endregion

    public VariableBuilder boolType() {
        return type("BOOL");
    }

    public VariableBuilder pointerType(String pointsTo) {
        return type(new PointerTypeDeclaration(pointsTo));
    }

    public VariableBuilder stringType(String base,
                                      ScalarValue<? extends AnyInt, Long> length,
                                      ScalarValue<? extends IECString, String> def) {
        StringTypeDeclaration std = new StringTypeDeclaration();
        std.setBaseTypeName(base);
        std.setSize(length);
        std.setInitialization(def);
        return type(std);
    }


    public VariableBuilder setBaseType(String baseType) {
        return type(baseType);
    }

    private VariableBuilder type(String baseType) {
        SimpleTypeDeclaration td = new SimpleTypeDeclaration();
        td.setBaseTypeName(baseType);
        return type(td);
    }


    public VariableBuilder type(TypeDeclaration type) {
        this.type = type;
        return this;
    }

    public VariableBuilder setInitialization(Initialization initialization) {
        this.initialization = initialization;
        return this;
    }

    public VariableBuilder create() {
        for (String id : identifiers) {
            VariableDeclaration vd = new VariableDeclaration(id, peek(), type);
            this.scope.add(vd);
        }
        return this;
    }

    public VariableBuilder close() {
        return create().clear();
    }

    public VariableBuilder identifiers(List<String> ast) {
        identifiers = ast;
        return this;
    }

    public void setPosition(ParserRuleContext start, Token end) {
        setPosition(start.getStart(), end);
    }

    public void setPosition(Token start, ParserRuleContext end) {
        setPosition(start, end.getStop());
    }

    public void setPosition(Token start, Token end) {
        pStart = new Top.Position(start.getLine(), start.getCharPositionInLine());
        pEnd = new Top.Position(end.getLine(), end.getCharPositionInLine());

    }
}
