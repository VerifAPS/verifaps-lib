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

import edu.kit.iti.formal.automation.analysis.ResolveDataTypes;
import edu.kit.iti.formal.automation.datatypes.*;
import edu.kit.iti.formal.automation.exceptions.DataTypeNotDefinedException;
import edu.kit.iti.formal.automation.st.ast.*;
import lombok.Data;

import java.io.Serializable;
import java.util.*;

/**
 * Created by weigl on 24.11.16.
 *
 * @author weigl, Augusto Modanese
 * @version $Id: $Id
 */
@Data
public class GlobalScope implements Serializable {
    private Map<String, ProgramDeclaration> programs = new HashMap<>();
    private Map<String, FunctionBlockDeclaration> fb = new HashMap<>();
    private Map<String, FunctionDeclaration> functions = new HashMap<>();
    private Map<String, TypeDeclaration> dataTypes = new HashMap<>();
    private List<FunctionResolver> functionResolvers = new LinkedList<>();
    private TypeScope types = TypeScope.builtin();
    private Map<String, ClassDeclaration> classes = new LinkedHashMap<>();
    private Map<String, InterfaceDeclaration> interfaces = new LinkedHashMap<>();
    private LocalScope globalVariableList = new LocalScope();

    /**
     * <p>defaultScope.</p>
     *
     * @return a {@link edu.kit.iti.formal.automation.scope.GlobalScope} object.
     */
    public static GlobalScope defaultScope() {
        GlobalScope g = new GlobalScope();
        g.functionResolvers.add(new DefinedFunctionResolver());
        g.functionResolvers.add(new FunctionResolverMUX());
        return g;
    }

    /**
     * <p>getProgram.</p>
     *
     * @param key a {@link java.lang.Object} object.
     * @return a {@link edu.kit.iti.formal.automation.st.ast.ProgramDeclaration} object.
     */
    public ProgramDeclaration getProgram(Object key) {
        return programs.get(key);
    }

    public List<ProgramDeclaration> getPrograms() {
        return new ArrayList<>(programs.values());
    }

    /**
     * <p>getCalleeName.</p>
     *
     * @param key a {@link java.lang.Object} object.
     * @return a {@link edu.kit.iti.formal.automation.st.ast.FunctionBlockDeclaration} object.
     */
    public FunctionBlockDeclaration getFunctionBlock(Object key) {
        return fb.get(key);
    }

    public List<FunctionBlockDeclaration> getFunctionBlocks() {
        return new ArrayList<>(fb.values());
    }

    /**
     * <p>getInvoked.</p>
     *
     * @param key a {@link java.lang.Object} object.
     * @return a {@link edu.kit.iti.formal.automation.st.ast.FunctionDeclaration} object.
     */
    public FunctionDeclaration getFunction(String key) {
        return functions.get(key);
    }

    /**
     * <p>registerProgram.</p>
     *
     * @param programDeclaration a {@link edu.kit.iti.formal.automation.st.ast.ProgramDeclaration} object.
     */
    public void registerProgram(ProgramDeclaration programDeclaration) {
        programs.put(programDeclaration.getIdentifier(), programDeclaration);
    }

    /**
     * <p>registerFunction.</p>
     *
     * @param functionDeclaration a {@link edu.kit.iti.formal.automation.st.ast.FunctionDeclaration} object.
     */
    public void registerFunction(FunctionDeclaration functionDeclaration) {
        functions.put(functionDeclaration.getIdentifier(), functionDeclaration);
    }

    /**
     * <p>registerFunctionBlock.</p>
     *
     * @param fblock a {@link edu.kit.iti.formal.automation.st.ast.FunctionBlockDeclaration} object.
     */
    public void registerFunctionBlock(FunctionBlockDeclaration fblock) {
        fb.put(fblock.getIdentifier(), fblock);
    }

    /**
     * <p>registerType.</p>
     *
     * @param dt a {@link edu.kit.iti.formal.automation.st.ast.TypeDeclaration} object.
     */
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
            System.out.println("ambguity fb vs. type");
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

        throw new DataTypeNotDefinedException("Could not find: " + name);
    }

    /**
     * <p>resolveFunction.</p>
     *
     * @param invocation a {@link Invocation} object.
     * @param local        a {@link edu.kit.iti.formal.automation.scope.LocalScope} object.
     * @return a {@link edu.kit.iti.formal.automation.st.ast.FunctionDeclaration} object.
     */
    public FunctionDeclaration resolveFunction(Invocation invocation,
            LocalScope local) {
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

    public ClassDeclaration resolveClass(String key) {
        ClassDeclaration classDeclaration = classes.get(key);
        if (classDeclaration == null)
            classDeclaration = getFunctionBlock(key);
        return classDeclaration;
    }

    public List<ClassDeclaration> getClasses() {
        return new ArrayList<>(classes.values());
    }

    public void registerInterface(InterfaceDeclaration interfaceDeclaration) {
        interfaces.put(interfaceDeclaration.getName(), interfaceDeclaration);
    }

    public InterfaceDeclaration resolveInterface(String key) {
        return interfaces.get(key);
    }

    public List<InterfaceDeclaration> getInterfaces() {
        return new ArrayList<>(interfaces.values());
    }

    public GlobalScope clone() {
        GlobalScope gs = new GlobalScope();
        gs.classes = new HashMap<>(classes);
        gs.interfaces = new HashMap<>(interfaces);
        gs.dataTypes = new HashMap<>(dataTypes);
        gs.fb = new HashMap<>(fb);
        gs.functionResolvers = new ArrayList<>(functionResolvers);
        gs.functions = new HashMap<>(functions);
        gs.programs = new HashMap<>(programs);
        gs.types = types.clone();
        // Needed to resolve circular dependency
        globalVariableList.setGlobalScope(null);
        gs.globalVariableList = globalVariableList.copy();
        gs.globalVariableList.setGlobalScope(this);
        globalVariableList.setGlobalScope(this);
        return gs;
    }
}
