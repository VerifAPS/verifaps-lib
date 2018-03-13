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

import com.google.common.collect.ImmutableMap;
import edu.kit.iti.formal.automation.datatypes.Any;
import edu.kit.iti.formal.automation.scope.InstanceScope;
import edu.kit.iti.formal.automation.st.Identifiable;
import edu.kit.iti.formal.automation.visitors.Visitor;
import lombok.Data;
import lombok.EqualsAndHashCode;
import lombok.ToString;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.HashSet;
import java.util.Map;
import java.util.Set;

/**
 * Created by weigla on 09.06.2014.
 *
 * @author weigl, Augusto Modanese
 * @version $Id: $Id
 */
@Data
@EqualsAndHashCode(callSuper = true, exclude = "parent")
@ToString(callSuper = true, exclude = "parent")
public class VariableDeclaration extends Top
        implements Comparable<VariableDeclaration>, Identifiable {
    /**
     * Constant <code>INPUT=1</code>
     */
    public static final int INPUT = 1;
    /**
     * Constant <code>OUTPUT=2</code>
     */
    public static final int OUTPUT = 2;
    /**
     * Constant <code>INOUT=4</code>
     */
    public static final int INOUT = 4;
    /**
     * Constant <code>LOCAL=8</code>
     */
    public static final int LOCAL = 8;
    /**
     * Constant <code>GLOBAL=16</code>
     */
    public static final int GLOBAL = 16;
    /**
     * Constant <code>CONSTANT=32</code>
     */
    public static final int CONSTANT = 32;
    /**
     * Constant <code>RETAIN=64</code>
     */
    public static final int RETAIN = 64;
    /**
     * Constant <code>LOCATED=128</code>
     */
    public static final int LOCATED = 128;
    /**
     * Constant <code>EXTERNAL=256</code>
     */
    public static final int EXTERNAL = 256;
    /**
     * Constant <code>TEMP=512</code>
     */
    public static final int TEMP = 512;

    /**
     * Constant <code>WRITTEN_TO=1024</code>
     */
    public static final int WRITTEN_TO = 1024;
    /**
     * Constant <code>READED=2048</code>
     */
    public static final int READED = 2048;
    /**
     * Constant <code>WRITE_BEFORE_READ=2 * 4096</code>
     */
    public static final int WRITE_BEFORE_READ = 2 * 4096;

    /**
     * Constant <code>FIRST_FREE=1 &lt;&lt; 16</code>
     */
    public static final int FIRST_FREE = 1 << 16;
    /**
     * Constant <code>NOT_READ=4096</code>
     */
    public static final int NOT_READ = 4096;

    // Access specifiers
    public static final int PUBLIC = 1 << 20;
    public static final int INTERNAL = 1 << 21;
    public static final int PROTECTED = 1 << 22;
    public static final int PRIVATE = 1 << 23;

    public static final Map<AccessSpecifier, Integer> ACCESS_SPECIFIER_DICT = ImmutableMap.of(
            AccessSpecifier.PUBLIC, PUBLIC,
            AccessSpecifier.INTERNAL, INTERNAL,
            AccessSpecifier.PROTECTED, PROTECTED,
            AccessSpecifier.PRIVATE, PRIVATE);

    private String name;
    private Any dataType;
    private int type;
    private TypeDeclaration typeDeclaration;

    /**
     * The top level scope element the variable is declared in.
     */
    private TopLevelScopeElement parent;

    /**
     * Set of instances which this variable can assume. Populated by static analysis.
     */
    private final Set<InstanceScope.Instance> instances = new HashSet<>();

    /**
     * <p>Constructor for VariableDeclaration.</p>
     */
    public VariableDeclaration() {

    }

    /**
     * <p>Constructor for VariableDeclaration.</p>
     *
     * @param name a {@link java.lang.String} object.
     * @param td   a {@link edu.kit.iti.formal.automation.st.ast.TypeDeclaration} object.
     */
    public VariableDeclaration(@NotNull String name, @NotNull TypeDeclaration td) {
        this();
        this.name = name;
        typeDeclaration = td;
        dataType = td.dataType;
    }

    /**
     * <p>Constructor for VariableDeclaration.</p>
     *
     * @param name     a {@link java.lang.String} object.
     * @param dataType a {@link edu.kit.iti.formal.automation.datatypes.Any} object.
     */
    public VariableDeclaration(@NotNull String name, @NotNull Any dataType) {
        this(name, new SimpleTypeDeclaration(dataType));
        this.dataType = dataType;
    }

    /**
     * <p>Constructor for VariableDeclaration.</p>
     *
     * @param value a {@link edu.kit.iti.formal.automation.st.ast.VariableDeclaration} object.
     */
    public VariableDeclaration(@NotNull VariableDeclaration value) {
        this(value.getName(), value.getType(), value.getTypeDeclaration());
        dataType = value.dataType;
        typeDeclaration = value.typeDeclaration;
    }

    /**
     * <p>Constructor for VariableDeclaration.</p>
     *
     * @param name  a {@link java.lang.String} object.
     * @param flags a int.
     * @param td    a {@link edu.kit.iti.formal.automation.st.ast.TypeDeclaration} object.
     */
    public VariableDeclaration(@NotNull String name, int flags, @NotNull TypeDeclaration td) {
        this.name = name;
        type = flags;
        typeDeclaration = td;
    }

    /**
     * <p>Constructor for VariableDeclaration.</p>
     *
     * @param name  a {@link java.lang.String} object.
     * @param flags a int.
     * @param dt    a {@link edu.kit.iti.formal.automation.datatypes.Any} object.
     */
    public VariableDeclaration(@NotNull String name, int flags, @NotNull Any dt) {
        this(name, dt);
        setType(flags);
    }

    /**
     * <p>Getter for the field <code>name</code>.</p>
     *
     * @return a {@link java.lang.String} object.
     */
    public String getName() {
        return name;
    }

    /**
     * <p>Setter for the field <code>name</code>.</p>
     *
     * @param name a {@link java.lang.String} object.
     */
    public void setName(@NotNull String name) {
        this.name = name;
    }

    /**
     * <p>getInit.</p>
     *
     * @return a {@link edu.kit.iti.formal.automation.st.ast.Initialization} object.
     */
    @Nullable
    public Initialization getInit() {
        if (typeDeclaration == null)
            return null;
        return typeDeclaration.initialization;
    }

    public void setInit(Initialization init) {
        this.typeDeclaration.setInitialization(init);
    }

    /**
     * <p>getDataTypeName.</p>
     *
     * @return a {@link java.lang.String} object.
     */
    @Nullable
    public String getDataTypeName() {
        if (dataType != null)
            return dataType.getName();
        if (typeDeclaration != null)
            return typeDeclaration.getTypeName();
        return null;
    }

    /**
     * <p>Getter for the field <code>dataType</code>.</p>
     *
     * @return a {@link edu.kit.iti.formal.automation.datatypes.Any} object.
     */
    public Any getDataType() {
        return dataType;
    }

    /**
     * <p>Setter for the field <code>dataType</code>.</p>
     *
     * @param dataType a {@link edu.kit.iti.formal.automation.datatypes.Any} object.
     */
    public void setDataType(@NotNull Any dataType) {
        this.dataType = dataType;
    }

    /**
     * <p>Getter for the field <code>type</code>.</p>
     *
     * @return a int.
     */
    public int getType() {
        return type;
    }

    /**
     * <p>Setter for the field <code>type</code>.</p>
     *
     * @param type a int.
     */
    public void setType(int type) {
        this.type = type;
    }

    /**
     * <p>is.</p>
     *
     * @param i a int.
     * @return a boolean.
     */
    public boolean is(int i) {
        return (type & i) != 0;
    }

    /**
     * <p>isRetain.</p>
     *
     * @return a boolean.
     */
    public boolean isRetain() {
        return is(RETAIN);
    }

    /**
     * <p>isConstant.</p>
     *
     * @return a boolean.
     */
    public boolean isConstant() {
        return is(CONSTANT);
    }

    /**
     * <p>isExternal.</p>
     *
     * @return a boolean.
     */
    public boolean isExternal() {
        return is(EXTERNAL);
    }

    /**
     * <p>isTemp.</p>
     *
     * @return a boolean.
     */
    public boolean isTemp() {
        return is(TEMP);
    }

    /**
     * <p>isLocated.</p>
     *
     * @return a boolean.
     */
    public boolean isLocated() {
        return is(LOCATED);
    }

    /**
     * <p>isLocal.</p>
     *
     * @return a boolean.
     */
    public boolean isLocal() {
        return is(LOCAL);
    }

    /**
     * <p>isOutput.</p>
     *
     * @return a boolean.
     */
    public boolean isOutput() {
        return is(OUTPUT);
    }

    /**
     * <p>isInput.</p>
     *
     * @return a boolean.
     */
    public boolean isInput() {
        return is(INPUT);
    }

    /**
     * <p>isInOut.</p>
     *
     * @return a boolean.
     */
    public boolean isInOut() {
        return is(INOUT);
    }

    /**
     * <p>isGlobal.</p>
     *
     * @return a boolean.
     */
    public boolean isGlobal() {
        return is(GLOBAL);
    }

    public boolean isPublic() {
        return is(PUBLIC);
    }

    public boolean isInternal() {
        return is(INTERNAL);
    }

    public boolean isProtected() {
        return is(PROTECTED);
    }

    public boolean isPrivate() {
        return is(PRIVATE);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public <T> T accept(@NotNull Visitor<T> visitor) {
        return visitor.visit(this);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public int compareTo(@NotNull VariableDeclaration o) {
        return getName().compareTo(o.getName());
    }

    /**
     * <p>Setter for the field <code>typeDeclaration</code>.</p>
     *
     * @param typeDeclaration a {@link edu.kit.iti.formal.automation.st.ast.TypeDeclaration} object.
     *                        <b>shared data</b>
     */
    public void setTypeDeclaration(@NotNull TypeDeclaration<?> typeDeclaration) {
        this.typeDeclaration = typeDeclaration;
    }

    /**
     * <p>Getter for the field <code>typeDeclaration</code>.</p>
     *
     * @return a {@link edu.kit.iti.formal.automation.st.ast.TypeDeclaration} object.
     */
    public TypeDeclaration getTypeDeclaration() {
        return typeDeclaration;
    }

    public void addInstance(@NotNull InstanceScope.Instance instance) {
        instances.add(instance);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean equals(@Nullable Object o) {
        if (this == o)
            return true;
        if (o == null || getClass() != o.getClass())
            return false;

        VariableDeclaration that = (VariableDeclaration) o;

        return name.equals(that.name);
    }

    @NotNull
    @Override public VariableDeclaration copy() {
        VariableDeclaration vd = new VariableDeclaration(name, type,
                typeDeclaration);
        vd.dataType = dataType;
        vd.setInit(getInit());
        return vd;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public int hashCode() {
        return name.hashCode();
    }

    /**
     * {@inheritDoc}
     */
    @Nullable
    @Override
    public String toString() {
        return name + " : " + getDataTypeName() + " := " + getInit();
    }

    @Override
    public String getIdentifier() {
        return name;
    }
}
