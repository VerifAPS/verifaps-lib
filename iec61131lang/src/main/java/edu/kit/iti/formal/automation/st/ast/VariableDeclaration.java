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
import edu.kit.iti.formal.automation.datatypes.AnyDt;
import edu.kit.iti.formal.automation.st.Identifiable;
import edu.kit.iti.formal.automation.visitors.Visitor;
import lombok.Getter;
import lombok.Setter;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.Map;

/**
 * Created by weigla on 09.06.2014.
 *
 * @author weigl, Augusto Modanese
 * @version $Id: $Id
 */
public class VariableDeclaration extends Top
        implements Comparable<VariableDeclaration>, Identifiable {
    public static final FlagCounter FLAG_COUNTER = new FlagCounter();

    /**
     * Constant <code>INPUT=1</code>
     */
    public static final int INPUT = FLAG_COUNTER.get();
    public static final int OUTPUT = FLAG_COUNTER.get();
    public static final int INOUT = FLAG_COUNTER.get(); //INPUT | OUTPUT;
    public static final int LOCAL = FLAG_COUNTER.get();
    public static final int GLOBAL = FLAG_COUNTER.get();
    public static final int CONSTANT = FLAG_COUNTER.get();
    public static final int RETAIN = FLAG_COUNTER.get();
    public static final int LOCATED = FLAG_COUNTER.get();
    public static final int EXTERNAL = FLAG_COUNTER.get();
    public static final int TEMP = FLAG_COUNTER.get();

    /**
     * Constant <code>WRITTEN_TO=1024</code>
     */
    public static final int WRITTEN_TO = FLAG_COUNTER.get();
    /**
     * Constant <code>READED=2048</code>
     */
    public static final int READED = FLAG_COUNTER.get();
    /**
     * Constant <code>WRITE_BEFORE_READ=2 * 4096</code>
     */
    public static final int WRITE_BEFORE_READ = FLAG_COUNTER.get();
    /**
     * Constant <code>NOT_READ=4096</code>
     */
    public static final int NOT_READ = FLAG_COUNTER.get();

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

    @Getter
    @Setter
    private String name;

    @Getter
    private AnyDt dataType;

    private int type;

    private TypeDeclaration typeDeclaration;

    /**
     * The top level scope element the variable belongs to.
     */
    @Deprecated
    @Getter
    @Setter
    private TopLevelScopeElement parent;

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
     * @param dataType a {@link edu.kit.iti.formal.automation.datatypes.AnyDt} object.
     */
    public VariableDeclaration(@NotNull String name, @NotNull AnyDt dataType) {
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
        this(name, td);
        type = flags;
    }

    /**
     * <p>Constructor for VariableDeclaration.</p>
     *
     * @param name  a {@link java.lang.String} object.
     * @param flags a int.
     * @param dt    a {@link edu.kit.iti.formal.automation.datatypes.AnyDt} object.
     */
    public VariableDeclaration(@NotNull String name, int flags, @NotNull AnyDt dt) {
        this(name, dt);
        setType(flags);
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

    public void setDataType(@NotNull AnyDt dataType) {
        this.dataType = dataType;
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
        return isInput() && isOutput();
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
     * {@inheritDoc}
     */
    @Override
    public String toString() {
        return name + " : " + getDataTypeName() + ":=" + getInit();
    }

    /**
     * <p>Getter for the field <code>typeDeclaration</code>.</p>
     *
     * @return a {@link edu.kit.iti.formal.automation.st.ast.TypeDeclaration} object.
     */
    public TypeDeclaration getTypeDeclaration() {
        return typeDeclaration;
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
     * {@inheritDoc}
     */
    @Override
    public boolean equals(Object o) {
        if (this == o)
            return true;
        if (o == null || getClass() != o.getClass())
            return false;

        VariableDeclaration that = (VariableDeclaration) o;

        return name.equals(that.name);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public int hashCode() {
        return name.hashCode();
    }

    @Override
    public VariableDeclaration copy() {
        VariableDeclaration vd = new VariableDeclaration(name, type, typeDeclaration);
        if (dataType != null)
            vd.setDataType(dataType);
        vd.setInit(getInit());
        vd.setParent(vd.getParent());
        return vd;
    }

    @Override
    public String getIdentifier() {
        return name;
    }

    public static class FlagCounter {
        private int internal = 1;

        public int peek() {
            return internal;
        }

        public int get() {
            int p = peek();
            internal <<= 1;
            return p;
        }
    }
}
