package edu.kit.iti.formal.stvs.model.code;

import edu.kit.iti.formal.stvs.model.common.IOVariable;
import edu.kit.iti.formal.stvs.model.expressions.Type;

import java.util.List;
import java.util.Set;

/**
 * Created by philipp on 09.01.17.
 */
public class ParsedCode {

    private List<FoldableCodeBlock> foldableCodeBlocks;
    private Set<IOVariable> definedVariables;
    private Set<Type> definedTypes;

    public ParsedCode(List<FoldableCodeBlock> foldableCodeBlocks, Set<IOVariable> definedVariables, Set<Type> definedTypes) {
        this.foldableCodeBlocks = foldableCodeBlocks;
        this.definedVariables = definedVariables;
        this.definedTypes = definedTypes;
    }

    public List<FoldableCodeBlock> getFoldableCodeBlocks() {
        return foldableCodeBlocks;
    }

    public Set<IOVariable> getDefinedVariables() {
        return definedVariables;
    }

    public Set<Type> getDefinedTypes() {
        return definedTypes;
    }
}
