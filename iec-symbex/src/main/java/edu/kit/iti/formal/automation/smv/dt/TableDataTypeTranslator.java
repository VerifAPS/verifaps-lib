package edu.kit.iti.formal.automation.smv.dt;

import edu.kit.iti.formal.automation.datatypes.Any;
import edu.kit.iti.formal.automation.st.ast.VariableDeclaration;
import edu.kit.iti.formal.smv.ast.SMVType;
import edu.kit.iti.formal.smv.ast.SVariable;
import lombok.Getter;

import java.util.HashMap;
import java.util.Map;

/**
 * @author Alexander Weigl
 */
public class TableDataTypeTranslator implements TypeTranslator {
    /**
     */
    private Map<Any, SMVType> map = new HashMap<>();

    /**
     *
     */
    @Getter
    private Map<String, Integer> integerMap = new HashMap<>();

    private DataTypeTranslator dttFallback = new DataTypeTranslator();

    /**
     *
     *
     */
    @Override
    public SMVType translate(Any datatype) {
        return map.computeIfAbsent(datatype, dttFallback::translate);
    }

    /**
     * {@inheritDoc}
     *
     * @param vdecl
     * @return
     */
    @Override
    public SVariable translate(VariableDeclaration vdecl) {
        if (integerMap.containsKey(vdecl.getName())) {
            int i = integerMap.get(vdecl.getName());
            if (i == 0)
                return SVariable.create(vdecl.getName()).asBool();
            return SVariable.create(vdecl.getName()).with(i < 0 ? SMVType.unsigned(-i) : SMVType.signed(i));
        } else {
            return SVariable.create(vdecl.getName()).with(translate(vdecl.getDataType()));
        }
    }
}
