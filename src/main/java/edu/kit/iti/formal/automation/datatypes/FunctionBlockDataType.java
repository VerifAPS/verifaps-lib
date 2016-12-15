package edu.kit.iti.formal.automation.datatypes;

import edu.kit.iti.formal.automation.st.ast.FunctionBlockDeclaration;

/**
 * Created by weigl on 25.11.16.
 */
public class FunctionBlockDataType extends RecordType {
    private final FunctionBlockDeclaration functionBlock;

    public FunctionBlockDataType(FunctionBlockDeclaration fb) {
        super(fb.getBlockName());
        functionBlock = fb;
    }

    @Override
    public String repr(Object obj) {
        return "not possible";
    }
}
