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
import java.util.function.Supplier;
import java.util.stream.Collectors;
import java.util.stream.Stream;

/**
 * @author Alexander Weigl
 * @version 1 (13.06.14)
 */
@Data
@NoArgsConstructor
public class Scope implements Visitable, Iterable<VariableDeclaration>, Copyable<Scope> {
    private final VariableScope variables = new VariableScope();
    private final Namespace<ActionDeclaration> actions = new Namespace<>();
    private Scope parent;
    private Namespace<ProgramDeclaration> programs = new Namespace<>();
    private Namespace<FunctionBlockDeclaration> functionBlocks = new Namespace<>();
    private Namespace<FunctionDeclaration> functions = new Namespace<>();
    private Namespace<TypeDeclaration> dataTypes = new Namespace<>();
    private List<FunctionResolver> functionResolvers = new LinkedList<>();
    private TypeScope types = TypeScope.builtin();
    private Namespace<ClassDeclaration> classes = new Namespace<>();
    private Namespace<InterfaceDeclaration> interfaces = new Namespace<>();

    public Scope(Scope parent) {
        setParent(parent);
    }

    public static Scope defaultScope() {
        Scope g = new Scope();
        g.functionResolvers.add(new DefinedFunctionResolver());
        g.functionResolvers.add(new FunctionResolverMUX());
        return g;
    }

    public void setParent(Scope parent) {
        if (parent != null) {
            programs.parent = parent::getPrograms;
            functionBlocks.parent = parent::getFunctionBlocks;
            functions.parent = parent::getFunctions;
            actions.parent = parent::getActions;
            classes.parent = parent::getClasses;
            dataTypes.parent = parent::getDataTypes;
            interfaces.parent = parent::getInterfaces;
        } else {
            programs.parent = null;
            functionBlocks.parent = null;
            functions.parent = null;
            actions.parent = null;
            classes.parent = null;
            dataTypes.parent = null;
            interfaces.parent = null;
        }
        this.parent = parent;
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

    public @Nullable VariableDeclaration getVariable(String s) {
        if (variables.containsKey(s)) {
            return variables.get(s);
        }

        if (parent != null)
            return parent.getVariable(s);
        return null;
    }

    public boolean hasVariable(String variable) {
        return variables.containsKey(variable) ||
                (parent != null && parent.hasVariable(variable));
    }

    public ProgramDeclaration getProgram(String key) {
        return programs.lookup(key);
    }

    public FunctionBlockDeclaration getFunctionBlock(String key) {
        return functionBlocks.lookup(key);
    }


    public FunctionDeclaration getFunction(String key) {
        return functions.lookup(key);
    }

    public void registerProgram(ProgramDeclaration programDeclaration) {
        programs.register(programDeclaration.getIdentifier(), programDeclaration);
    }

    public void registerFunction(FunctionDeclaration functionDeclaration) {
        functions.register(functionDeclaration.getIdentifier(), functionDeclaration);
    }

    public void registerFunctionBlock(FunctionBlockDeclaration fblock) {
        functionBlocks.register(fblock.getIdentifier(), fblock);
    }

    public void registerType(TypeDeclaration dt) {
        dataTypes.register(dt.getTypeName(), dt);
    }

    /**
     * <p>resolveDataType.</p>
     *
     * @param name a {@link java.lang.String} object.
     * @return a {@link edu.kit.iti.formal.automation.datatypes.AnyDt} object.
     */
    public AnyDt resolveDataType(String name) {
        if (types.containsKey(name))
            return types.get(name);

        boolean a = functionBlocks.containsKey(name);
        boolean b = dataTypes.containsKey(name);
        boolean c = classes.containsKey(name);
        boolean d = interfaces.containsKey(name);

        if (a && b || a && c || b && c) {
            System.err.println("Ambguity in Name Resolution for: " + name);
        }

        AnyDt q;
        if (a) {
            q = new FunctionBlockDataType(functionBlocks.lookup(name));
            types.put(name, q);
            return q;
        }

        if (b) {
            q = dataTypes.lookup(name).getDataType(this);
            types.put(name, q);
            return q;
        }

        if (c) {
            q = new ClassDataType(classes.lookup(name));
            types.put(name, q);
            return q;
        }

        if (d) {
            q = new InterfaceDataType(interfaces.lookup(name));
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

        //   throw new DataTypeNotDefinedException("Could not find: " + name);
        return null;
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
        classes.register(clazz.getIdentifier(), clazz);
    }

    @Nullable
    public ClassDeclaration resolveClass(String key) {
        return classes.lookup(key);
    }

    public void registerInterface(InterfaceDeclaration interfaceDeclaration) {
        interfaces.register(interfaceDeclaration.getName(), interfaceDeclaration);
    }

    public InterfaceDeclaration resolveInterface(String key) {
        return interfaces.lookup(key);
    }

    @Override
    public Scope copy() {
        Scope gs = new Scope(getParent());
        gs.classes = new Namespace<>(classes);
        gs.interfaces = new Namespace<>(interfaces);
        gs.dataTypes = new Namespace<>(dataTypes);
        gs.functionBlocks = new Namespace<>(functionBlocks);
        gs.functionResolvers = new ArrayList<>(functionResolvers);
        gs.functions = new Namespace<>(functions);
        gs.programs = new Namespace<>(programs);
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
        return actions.lookup(name);
    }

    public void registerAction(@NotNull ActionDeclaration a) {
        actions.register(a.getName(), a);
    }


    public class Namespace<T> {
        Supplier<Namespace<T>> parent;
        private HashMap<String, T> map = new LinkedHashMap<>();

        public Namespace(Namespace<T> other) {
            map.putAll(other.map);
            parent = other.parent;
        }

        public Namespace() {

        }

        public T lookup(String key) {
            if (map.containsKey(key)) return map.get(key);
            if (parent != null && parent.get() != null) parent.get().lookup(key);
            return null;
        }

        public void register(String key, T obj) {
            map.put(key, obj);
        }

        public Stream<T> getAll() {
            if (parent != null && parent.get() != null)
                return Stream.concat(parent.get().getAll(), map.values().stream());
            return map.values().stream();
        }

        public boolean containsKey(String name) {
            return map.containsKey(name);
        }

        public Collection<T> values() {
            return map.values();
        }
    }
}