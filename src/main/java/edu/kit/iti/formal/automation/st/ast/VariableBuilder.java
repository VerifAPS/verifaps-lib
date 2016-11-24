package edu.kit.iti.formal.automation.st.ast;

import edu.kit.iti.formal.automation.VariableScope;
import edu.kit.iti.formal.automation.datatypes.AnyInt;
import edu.kit.iti.formal.automation.datatypes.DataTypes;
import edu.kit.iti.formal.automation.datatypes.IECString;
import edu.kit.iti.formal.automation.datatypes.PointerType;
import edu.kit.iti.formal.automation.datatypes.values.ScalarValue;
import sun.reflect.generics.reflectiveObjects.NotImplementedException;

import java.util.Arrays;
import java.util.EmptyStackException;
import java.util.List;
import java.util.Stack;

/**
 * Created by weigl on 24.11.16.
 */
public class VariableBuilder {
    private final VariableScope scope;
    private Stack<Integer> stack = new Stack<>();

    public VariableBuilder(VariableScope scope) {
        this.scope = scope;
    }

    //region Handling of special flags (like constant, input or global)
    public void clear() {
        clear(0);
    }

    public void pop() {
        stack.pop();
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

    public void clear(int i) {
        stack.clear();
        stack.push(i);
    }

    public void mix(int i) {
        push(stack.pop() | i);
    }
    //endregion

    public void createBoolEdge(List<String> ast, boolean b) {
        throw new NotImplementedException();
    }


    public void create(String type, String... variables) {
        create(Arrays.asList(variables), type);
    }

    public void create(List<String> names, ArrayTypeDeclaration type) {
        for (String name : names) {
            VariableDeclaration var = new VariableDeclaration(name, peek());
            var.setDataTypeName(type.getTypeName());
            var.setDataType(type.asDataType());
            var.setInit((Initialization) type.getInitializationValue());
            scope.add(var);
        }
    }

    public void create(List<String> names, TypeDeclaration<?> init) {
        for (String name : names) {
            VariableDeclaration var = new VariableDeclaration(name, peek());
            var.setDataTypeName(init.getTypeName());
            var.setInit((Initialization) init.getInitializationValue());
            scope.add(var);
        }
    }

    public void create(List<String> names, StructureInitialization init) {
        for (String name : names) {
            VariableDeclaration var = new VariableDeclaration(name, peek(), init);
            var.setDataTypeName(init.getStructureName());
            scope.add(var);
        }
    }

    public void create(List<String> names, ScalarValue<?, ?> init) {
        for (String name : names) {
            VariableDeclaration var = new VariableDeclaration(name, peek(), init);
            scope.add(var);
        }
    }

    public void createPointers(List<String> names, String datatype) {
        for (String name : names) {
            VariableDeclaration var = new VariableDeclaration(name, peek(), null);
            var.setDataType(new PointerType(DataTypes.getDataType(datatype)));
            scope.add(var);
        }
    }

    public void create(List<String> ast, ScalarValue<? extends AnyInt, Long> length, ScalarValue<? extends IECString, String> def) {
        for (String name : ast) {
            VariableDeclaration var = new StringVariable(name, peek(), length, def);
            scope.add(var);
        }
    }


    public void create(List<String> ast, String baseType) {
        for (String name : ast) {
            VariableDeclaration var = new VariableDeclaration(name, peek());
            var.setDataTypeName(baseType);
            scope.add(var);
        }
    }


}
