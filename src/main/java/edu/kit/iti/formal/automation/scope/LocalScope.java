package edu.kit.iti.formal.automation.scope;

import edu.kit.iti.formal.automation.VariableScope;
import edu.kit.iti.formal.automation.exceptions.VariableNotDefinedException;
import edu.kit.iti.formal.automation.st.ast.*;
import edu.kit.iti.formal.automation.visitors.Visitable;
import edu.kit.iti.formal.automation.visitors.Visitor;

import java.util.*;
import java.util.function.Consumer;
import java.util.stream.Collectors;

/**
 *
 * @author Alexander Weigl
 * @version 1 (13.06.14)
 */
public class LocalScope implements Visitable, Iterable<VariableDeclaration> {
    private VariableScope localVariables = new VariableScope();
    private GlobalScope globalScope = new GlobalScope();

    public LocalScope() {
    }

    public LocalScope(GlobalScope global) {
        globalScope = global;
    }

    /**
     * Deep copy of the local scope.
     *
     * @param local
     */
    public LocalScope(LocalScope local) {
        globalScope = local.globalScope;
        for (Map.Entry<String, VariableDeclaration> e : local.localVariables.entrySet()) {
            localVariables.put(e.getKey(), new VariableDeclaration(e.getValue()));
        }
    }


    public Map<String, VariableDeclaration> getLocalVariables() {
        return localVariables;
    }

    public void setLocalVariables(VariableScope localVariables) {
        this.localVariables = localVariables;
    }


    public void add(VariableDeclaration var) {
        localVariables.put(var.getName(), var);
    }

    public <T> T visit(Visitor<T> visitor) {
        return visitor.visit(this);
    }

    public LocalScope prefixNames(String s) {
        LocalScope copy = new LocalScope();
        for (Map.Entry<String, VariableDeclaration> vd : this.localVariables.entrySet()) {
            VariableDeclaration nd = new VariableDeclaration(vd.getValue());
            nd.setName(s + nd.getName());
            copy.add(nd);
        }
        return copy;
    }

    @Override
    public Iterator<VariableDeclaration> iterator() {
        return localVariables.values().iterator();
    }

    @Override
    public void forEach(Consumer<? super VariableDeclaration> action) {
        localVariables.values().forEach(action);
    }

    @Override
    public Spliterator<VariableDeclaration> spliterator() {
        return localVariables.values().spliterator();
    }


    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder("LocalScope{");
        for (String s : localVariables.keySet()) {
            VariableDeclaration vd = localVariables.get(s);
            sb.append(s).append(":").append(vd.getDataType());
            if (vd.getInit() != null) sb.append(" := ").append(vd.getInit());
            sb.append("},");
        }
        sb.delete(sb.length() - 1, sb.length());
        sb.append("}");
        return sb.toString();
    }

    public VariableDeclaration getVariable(SymbolicReference reference)
            throws VariableNotDefinedException {
        if (localVariables.containsKey(reference.getIdentifier()))
            return localVariables.get(reference.getIdentifier());
        throw new VariableNotDefinedException(this, reference);
    }

    public void setGlobalScope(GlobalScope globalScope) {
        this.globalScope = globalScope;
    }

    public GlobalScope getGlobalScope() {
        return globalScope;
    }

    public VariableBuilder builder() {
        return new VariableBuilder(localVariables);
    }

    public List<VariableDeclaration> filterByFlags(int flags) {
        return localVariables.values().stream().filter((v) -> v.is(flags)).collect(Collectors.toList());
    }

    public VariableDeclaration getVariable(String s) {
        return localVariables.get(s);
    }
}