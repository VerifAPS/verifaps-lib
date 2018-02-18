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
import edu.kit.iti.formal.automation.analysis.ResolveDataTypes;
import edu.kit.iti.formal.automation.datatypes.*;
import edu.kit.iti.formal.automation.exceptions.DataTypeNotDefinedException;
import edu.kit.iti.formal.automation.exceptions.VariableNotDefinedException;
import edu.kit.iti.formal.automation.sfclang.ast.ActionDeclaration;
import edu.kit.iti.formal.automation.st.ast.*;
import edu.kit.iti.formal.automation.visitors.Visitable;
import edu.kit.iti.formal.automation.visitors.Visitor;
import lombok.Data;
import lombok.NoArgsConstructor;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.*;
import java.util.function.Consumer;
import java.util.function.Function;
import java.util.stream.Collectors;
import java.util.stream.Stream;

/**
 * @author Alexander Weigl
 * @version 1 (13.06.14)
 */
@Data
@NoArgsConstructor
public class Scope implements Visitable, Iterable<VariableDeclaration>, Copyable<Scope> {
    private VariableScope variables = new VariableScope();
    private Scope parent;
    private Map<String, ProgramDeclaration> programs = new HashMap<>();
    private Map<String, FunctionBlockDeclaration> fb = new HashMap<>();
    private Map<String, FunctionDeclaration> functions = new HashMap<>();
    private Map<String, TypeDeclaration> dataTypes = new HashMap<>();
    private List<FunctionResolver> functionResolvers = new LinkedList<>();
    private TypeScope types = TypeScope.builtin();
    private Map<String, ClassDeclaration> classes = new LinkedHashMap<>();
    private Map<String, InterfaceDeclaration> interfaces = new LinkedHashMap<>();
    private Map<String, ActionDeclaration> actions = new LinkedHashMap<>();

    public Scope(Scope parent) {
        this.parent = parent;
    }

    public static Scope defaultScope() {
        Scope g = new Scope();
        g.functionResolvers.add(new DefinedFunctionResolver());
        g.functionResolvers.add(new FunctionResolverMUX());
        return g;
    }

    public Map<String, VariableDeclaration> asMap() {
        return variables;
    }

    public void add(VariableDeclaration var) {
        variables.put(var.getName(), var);
    }

    /**
     * {@inheritDoc}
     */
    public <T> T accept(Visitor<T> visitor) {
        return visitor.visit(this);
    }

    public Scope prefixNames(String s) {
        Scope copy = new Scope();
        for (Map.Entry<String, VariableDeclaration> vd : this.variables.entrySet()) {
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
        return variables.values().iterator();
    }

    @Override
    public void forEach(Consumer<? super VariableDeclaration> action) {
        variables.values().forEach(action);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Spliterator<VariableDeclaration> spliterator() {
        return variables.values().spliterator();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder("Scope{");
        for (String s : variables.keySet()) {
            VariableDeclaration vd = variables.get(s);
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
        if (variables.containsKey(reference.getIdentifier()))
            return variables.get(reference.getIdentifier());
        throw new VariableNotDefinedException(this, reference);
    }

    /**
     * <p>builder.</p>
     *
     * @return a {@link edu.kit.iti.formal.automation.st.ast.VariableBuilder} object.
     */
    public VariableBuilder builder() {
        return new VariableBuilder(variables);
    }

    public List<VariableDeclaration> filterByFlags(int flags) {
        return variables.values().stream().filter((v) -> v.is(flags)).collect(Collectors.toList());
    }

    public VariableDeclaration getVariable(String s) {
        return variables.computeIfAbsent(s, getFromParent(s, parent::getVariable));
    }

    public boolean hasVariable(String variable) {
        return variables.containsKey(variable);
    }

    public ProgramDeclaration getProgram(String key) {
        return programs.computeIfAbsent(key, getFromParent(key, parent::getProgram));
    }

    public List<ProgramDeclaration> getPrograms() {
        return new ArrayList<>(programs.values());
    }

    public <T> Function<String, T> getFromParent(String key, Function<String, T> func) {
        return k -> {
            if (parent != null) {
                return func.apply(key);
            }
            return null;
        };
    }

    public FunctionBlockDeclaration getFunctionBlock(String key) {
        if (fb.containsKey(key)) return fb.get(key);
        if (parent != null) return parent.getFunctionBlock(key);
        return null;
    }

    public List<FunctionBlockDeclaration> getFunctionBlocks() {
        return new ArrayList<>(fb.values());
    }

    public FunctionDeclaration getFunction(String key) {
        return functions.computeIfAbsent(key, getFromParent(key, parent::getFunction));
    }

    public void registerProgram(ProgramDeclaration programDeclaration) {
        programs.put(programDeclaration.getIdentifier(), programDeclaration);
    }

    public void registerFunction(FunctionDeclaration functionDeclaration) {
        functions.put(functionDeclaration.getIdentifier(), functionDeclaration);
    }

    public void registerFunctionBlock(FunctionBlockDeclaration fblock) {
        fb.put(fblock.getIdentifier(), fblock);
    }

    public void registerType(TypeDeclaration dt) {
        dataTypes.put(dt.getTypeName(), dt);
    }

    /**
     * <p>resolveDataType.</p>
     *
     * @param name a {@link java.lang.String} object.
     * @return a {@link edu.kit.iti.formal.automation.datatypes.Any} object.
     */
    public Any resolveDataType(String name) {
        if (types.containsKey(name))
            return types.get(name);

        boolean a = fb.containsKey(name);
        boolean b = dataTypes.containsKey(name);
        boolean c = classes.containsKey(name);
        boolean d = interfaces.containsKey(name);

        if (a && b || a && c || b && c) {
            System.err.println("Ambguity in Name Resolution for: " + name);
        }

        Any q;
        if (a) {
            q = new FunctionBlockDataType(fb.get(name));
            types.put(name, q);
            return q;
        }

        if (b) {
            q = dataTypes.get(name).getDataType(this);
            types.put(name, q);
            return q;
        }

        if (c) {
            q = new ClassDataType(classes.get(name));
            types.put(name, q);
            return q;
        }

        if (d) {
            q = new InterfaceDataType(interfaces.get(name));
            types.put(name, q);
            return q;
        }

        // Reference
        if (name.length() > 7 && name.substring(0, 7).equals("REF_TO "))
            return new ReferenceType(resolveDataType(name.substring(7)));

        // Void
        if (name == "VOID")
            return DataTypes.VOID;

        if (parent != null)
            return parent.resolveDataType(name);

        throw new DataTypeNotDefinedException("Could not find: " + name);
    }

    public FunctionDeclaration resolveFunction(Invocation invocation, Scope local) {
        for (FunctionResolver fr : functionResolvers) {
            FunctionDeclaration decl = fr.resolve(invocation, local);
            if (decl != null)
                return decl;
        }
        return null;
    }

    /**
     * Used to make a class or interface to be known.
     *
     * @param clazz
     * @see ResolveDataTypes
     */
    public void registerClass(ClassDeclaration clazz) {
        classes.put(clazz.getIdentifier(), clazz);
    }

    @Nullable
    public ClassDeclaration resolveClass(String key) {
        ClassDeclaration classDeclaration = classes.get(key);
        if (classDeclaration == null)
            classDeclaration = getFunctionBlock(key);

        if (parent != null && classDeclaration == null)
            return parent.resolveClass(key);

        return classDeclaration;
    }

    @NotNull
    public List<ClassDeclaration> getClasses() {
        return new ArrayList<>(classes.values());
    }

    public void registerInterface(InterfaceDeclaration interfaceDeclaration) {
        interfaces.put(interfaceDeclaration.getName(), interfaceDeclaration);
    }

    public InterfaceDeclaration resolveInterface(String key) {
        if (interfaces.containsKey(key))
            return interfaces.get(key);
        if (parent != null)
            return parent.resolveInterface(key);
        return null;
    }

    public List<InterfaceDeclaration> getInterfaces() {
        return new ArrayList<>(interfaces.values());
    }


    @Override
    public Scope copy() {
        Scope gs = new Scope(getParent());
        gs.classes = new HashMap<>(classes);
        gs.dataTypes = new HashMap<>(dataTypes);
        gs.fb = new HashMap<>(fb);
        gs.functionResolvers = new ArrayList<>(functionResolvers);
        gs.functions = new HashMap<>(functions);
        gs.programs = new HashMap<>(programs);
        gs.types = types.clone();

        for (Map.Entry<String, VariableDeclaration> e : variables.entrySet()) {
            gs.variables.put(e.getKey(), e.getValue().copy());
        }
        return gs;
    }

    public void addVariables(Scope scope) {
        variables.putAll(scope.getVariables());
    }

    public Scope getTopLevel() {
        Scope s = this;
        while (s.getParent() != null) s = s.getParent();
        return s;
    }

    public Stream<VariableDeclaration> stream() {
        return asMap().values().stream();
    }

    @Nullable
    public ActionDeclaration getAction(@NotNull String name) {
        if (actions.containsKey(name))
            return actions.get(name);
        if (parent != null) {
            return parent.getAction(name);
        }
        return null;
    }

    public void registerAction(@NotNull ActionDeclaration a) {
        actions.put(a.getName(), a);
    }
}
