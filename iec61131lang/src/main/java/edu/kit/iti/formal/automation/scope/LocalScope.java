package edu.kit.iti.formal.automation.scope;



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
import edu.kit.iti.formal.automation.exceptions.VariableNotDefinedException;
import edu.kit.iti.formal.automation.st.ast.*;
import edu.kit.iti.formal.automation.visitors.Visitable;
import edu.kit.iti.formal.automation.visitors.Visitor;
import lombok.Data;
import lombok.RequiredArgsConstructor;
import org.jetbrains.annotations.NotNull;

import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Spliterator;
import java.util.function.Consumer;
import java.util.stream.Collectors;
import java.util.stream.Stream;

/**
 * <p>LocalScope class.</p>
 *
 * @author Alexander Weigl
 * @version 1 (13.06.14)
 */
@Data
@RequiredArgsConstructor
public class LocalScope implements Visitable, Iterable<VariableDeclaration>, Copyable<LocalScope> {
    private VariableScope localVariables = new VariableScope();
    private GlobalScope globalScope;

    private final TopLevelScopeElement parent;

    public LocalScope() {
        parent = null;
    }

    public LocalScope(@NotNull GlobalScope globalScope, TopLevelScopeElement parent) {
        this.globalScope = globalScope;
        this.parent = parent;
    }

    /**
     * Deep copy of the local scope.
     *
     * @param local a {@link edu.kit.iti.formal.automation.scope.LocalScope} object.
     */
    public LocalScope(LocalScope local) {
        globalScope = local.globalScope;
        parent = local.parent;
        for (Map.Entry<String, VariableDeclaration> e : local.localVariables.entrySet()) {
            VariableDeclaration variableDeclaration = new VariableDeclaration(e.getValue());
            variableDeclaration.setName(e.getKey());
            add(variableDeclaration);
        }
    }

    public LocalScope(List<VariableDeclaration> vars) {
        this();
        vars.forEach(this::add);
    }

    public Map<String, VariableDeclaration> asMap() {
        return localVariables;
    }

    /**
     * <p>add.</p>
     *
     * @param var a {@link edu.kit.iti.formal.automation.st.ast.VariableDeclaration} object.
     */
    public void add(VariableDeclaration var) {
        localVariables.put(var.getName(), var);
        if (var.getParent() == null)
            var.setParent(parent);
    }

    public void addAll(List<VariableDeclaration> vars) {
        vars.forEach(this::add);
    }

    public void addAll(VariableScope variableScope) {
        variableScope.values().forEach(this::add);
    }

    /**
     * {@inheritDoc}
     */
    public <T> T accept(Visitor<T> visitor) {
        return visitor.visit(this);
    }

    /**
     * <p>prefixNames.</p>
     *
     * @param s a {@link java.lang.String} object.
     * @return a {@link edu.kit.iti.formal.automation.scope.LocalScope} object.
     */
    public LocalScope prefixNames(String s) {
        LocalScope copy = new LocalScope(parent);
        for (Map.Entry<String, VariableDeclaration> vd : this.localVariables.entrySet()) {
            VariableDeclaration nd = new VariableDeclaration(vd.getValue());
            nd.setName(s + nd.getName());
            copy.add(nd);
        }
        return copy;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Iterator<VariableDeclaration> iterator() {
        return localVariables.values().iterator();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void forEach(Consumer<? super VariableDeclaration> action) {
        localVariables.values().forEach(action);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Spliterator<VariableDeclaration> spliterator() {
        return localVariables.values().spliterator();
    }

    public Stream<VariableDeclaration> stream() {
        return localVariables.values().stream();
    }

    public Stream<VariableDeclaration> parallelStream() {
        return localVariables.values().parallelStream();
    }

    /**
     * {@inheritDoc}
     */
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

    /**
     * <p>getVariable.</p>
     *
     * @param reference a {@link edu.kit.iti.formal.automation.st.ast.SymbolicReference} object.
     * @return a {@link edu.kit.iti.formal.automation.st.ast.VariableDeclaration} object.
     * @throws edu.kit.iti.formal.automation.exceptions.VariableNotDefinedException if any.
     */
    public VariableDeclaration getVariable(SymbolicReference reference)
            throws VariableNotDefinedException {
        if (localVariables.containsKey(reference.getIdentifier()))
            return localVariables.get(reference.getIdentifier());
        throw new VariableNotDefinedException(this, reference);
    }

    /**
     * <p>builder.</p>
     *
     * @return a {@link edu.kit.iti.formal.automation.st.ast.VariableBuilder} object.
     */
    public VariableBuilder builder() {
        return new VariableBuilder(localVariables);
    }

    /**
     * <p>filterByFlags.</p>
     *
     * @param flags a int.
     * @return a {@link java.util.List} object.
     */
    public List<VariableDeclaration> filterByFlags(int flags) {
        return localVariables.values().stream().filter((v) -> v.is(flags)).collect(Collectors.toList());
    }

    /**
     * <p>getVariable.</p>
     *
     * @param s a {@link java.lang.String} object.
     * @return a {@link edu.kit.iti.formal.automation.st.ast.VariableDeclaration} object.
     */
    public VariableDeclaration getVariable(String s) {
        return localVariables.get(s);
    }

    public boolean hasVariable(String variable) {
        return localVariables.containsKey(variable);
    }

    @Override
    public LocalScope copy() {
        LocalScope ls = new LocalScope(this);
        if (globalScope != null)
            ls.globalScope = globalScope.clone();
        for (Map.Entry<String, VariableDeclaration> e : localVariables.entrySet()) {
            VariableDeclaration variableDeclaration = new VariableDeclaration(e.getValue().copy());
            variableDeclaration.setName(e.getKey());
            ls.add(variableDeclaration);
        }
        return ls;
    }

    public LocalScope shallowCopy() {
        LocalScope ls = new LocalScope(parent);
        ls.globalScope = globalScope;
        ls.addAll(localVariables);
        return ls;
    }
}
