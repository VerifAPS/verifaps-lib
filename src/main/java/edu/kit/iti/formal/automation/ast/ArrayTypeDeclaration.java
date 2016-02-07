package edu.kit.iti.formal.automation.ast;

import edu.kit.iti.formal.automation.datatypes.Any;
import edu.kit.iti.formal.automation.datatypes.DataTypes;
import edu.kit.iti.formal.automation.visitors.Visitor;
import edu.kit.iti.formal.automation.datatypes.IECArray;

import java.util.ArrayList;
import java.util.List;

/**
 * Created by weigl on 13.06.14.
 */
public class ArrayTypeDeclaration extends TypeDeclaration<ArrayInitialization> {
    private List<Range> ranges = new ArrayList<>();

    @Override
    public <T> T visit(Visitor<T> visitor) {
        return visitor.visit(this);
    }

    public void addSubRange(Range ast) {
        ranges.add(ast);
    }

    public Any asDataType() {
        Any dt = DataTypes.getDataType(getBaseTypeName());
        IECArray array = new IECArray(getTypeName(), dt, ranges);
        return array;
    }
}
