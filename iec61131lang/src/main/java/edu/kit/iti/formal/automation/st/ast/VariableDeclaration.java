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

import edu.kit.iti.formal.automation.datatypes.Any;
import edu.kit.iti.formal.automation.visitors.Visitor;

/**
 * Created by weigla on 09.06.2014.
 *
 * @author weigl
 * @version $Id: $Id
 */
public class VariableDeclaration extends Top
        implements Comparable<VariableDeclaration> {
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

    private String name;
    private Any dataType;
    private int type;
    private TypeDeclaration typeDeclaration;

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
    public VariableDeclaration(String name, TypeDeclaration td) {
        this();
        this.name = name;
        typeDeclaration = td;
    }

    /**
     * <p>Constructor for VariableDeclaration.</p>
     *
     * @param name     a {@link java.lang.String} object.
     * @param dataType a {@link edu.kit.iti.formal.automation.datatypes.Any} object.
     */
    public VariableDeclaration(String name, Any dataType) {
        this.name = name;
        this.dataType = dataType;
    }

    /**
     * <p>Constructor for VariableDeclaration.</p>
     *
     * @param value a {@link edu.kit.iti.formal.automation.st.ast.VariableDeclaration} object.
     */
    public VariableDeclaration(VariableDeclaration value) {
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
    public VariableDeclaration(String name, int flags, TypeDeclaration td) {
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
    public VariableDeclaration(String name, int flags, Any dt) {
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
    public void setName(String name) {
        this.name = name;
    }

    /**
     * <p>getInit.</p>
     *
     * @return a {@link edu.kit.iti.formal.automation.st.ast.Initialization} object.
     */
    public Initialization getInit() {
        if (typeDeclaration == null)
            return null;
        return typeDeclaration.initialization;
    }

    /*public void setInit(Initialization init) {
        this.typeDeclaration.setInitialization(init);
    }*/

    /**
     * <p>getDataTypeName.</p>
     *
     * @return a {@link java.lang.String} object.
     */
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
    public void setDataType(Any dataType) {
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

    /**
     * {@inheritDoc}
     */
    @Override
    public <T> T accept(Visitor<T> visitor) {
        return visitor.visit(this);
    }

    /**
     * {@inheritDoc}
     */
    @Override public int compareTo(VariableDeclaration o) {
        return getName().compareTo(o.getName());
    }

    /**
     * {@inheritDoc}
     */
    @Override public String toString() {
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
    public void setTypeDeclaration(TypeDeclaration<?> typeDeclaration) {
        this.typeDeclaration = typeDeclaration;
    }

    /**
     * {@inheritDoc}
     */
    @Override public boolean equals(Object o) {
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
    @Override public int hashCode() {
        return name.hashCode();
    }

    @Override public VariableDeclaration copy() {
        VariableDeclaration vd = new VariableDeclaration(name, type,
                typeDeclaration);
        vd.setDataType(dataType);
        return vd;
    }
}
