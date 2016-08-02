package edu.kit.iti.formal.automation.datatypes;

import edu.kit.iti.formal.automation.st.ast.Range;

import java.util.ArrayList;
import java.util.List;

/**
 * Created by weigl on 07/10/14.
 */
public class IECArray extends Any {
    private final Any fieldType;
    private List<Range> ranges = new ArrayList<>();

    public IECArray(String name, Any fieldType, List<Range> ranges) {
        this.name = name;
        this.fieldType = fieldType;
        this.ranges = ranges;
    }

    public Any getFieldType() {
        return fieldType;
    }

    public List<Range> getRanges() {
        return ranges;
    }

    public void setRanges(List<Range> ranges) {
        this.ranges = ranges;
    }

    @Override
    public String repr(Object obj) {
        return null;
    }
}
