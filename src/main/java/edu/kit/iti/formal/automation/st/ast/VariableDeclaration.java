package edu.kit.iti.formal.automation.st.ast;


import edu.kit.iti.formal.automation.datatypes.Any;
import edu.kit.iti.formal.automation.visitors.Visitor;

/**
 * Created by weigla on 09.06.2014.
 */
public class VariableDeclaration
        extends Top implements Comparable<VariableDeclaration> {
    public static final int INPUT = 1;
    public static final int OUTPUT = 2;
    public static final int INOUT = 4;
    public static final int LOCAL = 8;
    public static final int GLOBAL = 16;
    public static final int CONSTANT = 32;
    public static final int RETAIN = 64;
    public static final int LOCATED = 128;
    public static final int EXTERNAL = 256;
    public static final int TEMP = 512;

    public static final int WRITTEN_TO = 1024;
    public static final int READED = 2048;
    public static final int WRITE_BEFORE_READ = 2 * 4096;

    public static final int FIRST_FREE = 1 << 16;
    public static final int NOT_READED = 4096;

    private String name;
    private Any dataType;
    private int type;
    private TypeDeclaration typeDeclaration;

    public VariableDeclaration() {

    }

    public VariableDeclaration(String name, TypeDeclaration td) {
        this();
        this.name = name;
        typeDeclaration = td;
    }

    public VariableDeclaration(String name, Any dataType) {
        this.name = name;
        this.dataType = dataType;
    }

    public VariableDeclaration(VariableDeclaration value) {
        this(value.getName(), value.getType(), value.getTypeDeclaration());
        dataType = value.dataType;
        typeDeclaration = value.typeDeclaration;
    }

    public VariableDeclaration(String name, int flags, TypeDeclaration td) {
        this.name = name;
        type = flags;
        typeDeclaration = td;
    }

    public String getName() {
        return name;
    }

    public void setName(String name) {
        this.name = name;
    }

    public Initialization getInit() {
        return typeDeclaration.getInitializationValue();
    }

    /*public void setInit(Initialization init) {
        this.typeDeclaration.setInitialization(init);
    }*/

    public String getDataTypeName() {
        if (dataType != null)
            return dataType.getName();
        if (typeDeclaration != null)
            return typeDeclaration.getTypeName();
        return null;
    }

    public Any getDataType() {
        return dataType;
    }

    public void setDataType(Any dataType) {
        this.dataType = dataType;
    }

    public int getType() {
        return type;
    }

    public void setType(int type) {
        this.type = type;
    }


    public boolean is(int i) {
        return (type & i) != 0;
    }

    public boolean isRetain() {
        return is(RETAIN);
    }

    public boolean isConstant() {
        return is(CONSTANT);
    }

    public boolean isExternal() {
        return is(EXTERNAL);
    }

    public boolean isTemp() {
        return is(TEMP);
    }

    public boolean isLocated() {
        return is(LOCATED);
    }

    public boolean isLocal() {
        return is(LOCAL);
    }

    public boolean isOutput() {
        return is(OUTPUT);
    }

    public boolean isInput() {
        return is(INPUT);
    }

    public boolean isInOut() {
        return is(INOUT);
    }

    public boolean isGlobal() {
        return is(GLOBAL);
    }

    public <T> T visit(Visitor<T> visitor) {
        return visitor.visit(this);
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        VariableDeclaration that = (VariableDeclaration) o;

        if (!name.equals(that.name)) return false;

        return true;
    }

    @Override
    public int hashCode() {
        return name.hashCode();
    }

    @Override
    public int compareTo(VariableDeclaration o) {
        return getName().compareTo(o.getName());
    }

    @Override
    public String toString() {
        return name + " : " + getDataTypeName() + ":=" + getInit();
    }

    public TypeDeclaration getTypeDeclaration() {
        return typeDeclaration;
    }

    /**
     * @param typeDeclaration
     * @dangerous, shared data
     */
    public void setTypeDeclaration(TypeDeclaration<?> typeDeclaration) {
        this.typeDeclaration = typeDeclaration;
    }
}
