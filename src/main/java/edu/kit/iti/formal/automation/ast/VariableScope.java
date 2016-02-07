package edu.kit.iti.formal.automation.ast;

import edu.kit.iti.formal.automation.datatypes.AnyInt;
import edu.kit.iti.formal.automation.datatypes.IECString;
import edu.kit.iti.formal.automation.visitors.Visitable;
import edu.kit.iti.formal.automation.datatypes.values.ScalarValue;
import edu.kit.iti.formal.automation.visitors.Visitor;

import java.util.*;
import java.util.function.Consumer;

/**
 * Created by weigl on 13.06.14.
 */
public class VariableScope implements Visitable, Iterable<VariableDeclaration> {
    private Map<String, VariableDeclaration> variableMap = new TreeMap<>();
    private Stack<Integer> stack = new Stack<>();

    public VariableScope() {
    }

    public VariableScope(VariableScope scope) {
        for (Map.Entry<String, VariableDeclaration> e : scope.variableMap.entrySet()) {
            variableMap.put(e.getKey(), new VariableDeclaration(e.getValue()));
        }
        stack.addAll(scope.stack);
    }


    public Map<String, VariableDeclaration> getVariableMap() {
        return variableMap;
    }

    public void setVariableMap(Map<String, VariableDeclaration> variableMap) {
        this.variableMap = variableMap;
    }

    public void push(int i) {
        stack.push(i);
    }

    public void clear() {
        stack.clear();
        stack.push(0);
    }

    public void clear(int i) {
        clear();
        push(i);
    }

    public void mix(int i) {
        push(stack.pop() | i);
    }

    public void addBoolEdge(List<String> ast, boolean b) {
        //TODO
    }


    public void add(VariableDeclaration var) {
        variableMap.put(var.getName(), var);
    }

    public void create(List<String> names, ArrayTypeDeclaration type) {
        for (String name : names) {
            VariableDeclaration var = new VariableDeclaration(name, peek());
            var.setDataTypeName(type.getTypeName());
            var.setDataType(type.asDataType());
            var.setInit((Initialization) type.getInitializationValue());
            add(var);
        }
    }

    public void create(List<String> names, TypeDeclaration<?> init) {
        for (String name : names) {
            VariableDeclaration var = new VariableDeclaration(name, peek());
            var.setDataTypeName(init.getTypeName());
            var.setInit((Initialization) init.getInitializationValue());
            add(var);
        }
    }

    public void createFBName(List<String> names, String s, StructureInitialization init) {
        throw new AssertionError("i do not know what this construct means");
        /*for(String name : names) {
            Variable var = new Variable(name, stack.peek(), init);
            var.setDataType(init.getStructureName());
            add(var);
        }*/
    }


    public void create(List<String> names, StructureInitialization init) {
        for (String name : names) {
            VariableDeclaration var = new VariableDeclaration(name, peek(), init);
            var.setDataTypeName(init.getStructureName());
            add(var);
        }
    }

    public void create(List<String> names, ScalarValue<?, ?> init) {
        for (String name : names) {
            VariableDeclaration var = new VariableDeclaration(name, peek(), init);
            add(var);
        }
    }


    public void pop() {
        stack.pop();
    }


    public void create(List<String> ast, ScalarValue<? extends AnyInt, Long> length, ScalarValue<? extends IECString, String> def) {
        for (String name : ast) {
            VariableDeclaration var = new StringVariable(name, peek(), length, def);
            add(var);
        }
    }

    public int peek() {
        try {
            return stack.peek();
        } catch (EmptyStackException e) {
            return 0;
        }
    }


    public void create(List<String> ast, String baseType) {
        for (String name : ast) {
            VariableDeclaration var = new VariableDeclaration(name, peek());
            var.setDataTypeName(baseType);
            add(var);
        }
    }

    public <T> T visit(Visitor<T> visitor) {
        return visitor.visit(this);
    }

    public void create(String type, String... variables) {
        create(Arrays.asList(variables), type);
    }

    public VariableScope prefixNames(String s) {
        VariableScope copy = new VariableScope();
        for (Map.Entry<String, VariableDeclaration> vd : this.variableMap.entrySet()) {
            VariableDeclaration nd = new VariableDeclaration(vd.getValue());
            nd.setName(s + nd.getName());
            copy.add(nd);
        }
        return copy;
    }

    @Override
    public Iterator<VariableDeclaration> iterator() {
        return variableMap.values().iterator();
    }

    @Override
    public void forEach(Consumer<? super VariableDeclaration> action) {
        variableMap.values().forEach(action);
    }

    @Override
    public Spliterator<VariableDeclaration> spliterator() {
        return variableMap.values().spliterator();
    }


    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder("VariableScope[");
        for (String s : variableMap.keySet()) {
            sb.append(s).append("={").append(variableMap.get(s)).append("},");
        }
        sb.delete(sb.length() - 1, sb.length());
        sb.append("]");
        return sb.toString();
    }
}