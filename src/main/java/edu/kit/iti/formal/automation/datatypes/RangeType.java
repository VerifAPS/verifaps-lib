package edu.kit.iti.formal.automation.datatypes;

/**
 * Created by weigl on 10.06.14.
 */
public class RangeType extends Any {
    private long bottom, top;
    private AnyInt base = AnyInt.INT;

    public RangeType(long bottom, long top, AnyInt base) {
        this.bottom = bottom;
        this.top = top;
    }

    public long getBottom() {
        return bottom;
    }

    public void setBottom(long bottom) {
        this.bottom = bottom;
    }

    public long getTop() {
        return top;
    }

    public void setTop(long top) {
        this.top = top;
    }

    public AnyInt getBase() {
        return base;
    }

    public void setBase(AnyInt base) {
        this.base = base;
    }

    @Override
    public String repr(Object obj) {
        return base.repr(obj);
    }


    @Override
    public <T> T accept(DataTypeVisitor<T> visitor) {
        return visitor.visit(this);
    }
}
