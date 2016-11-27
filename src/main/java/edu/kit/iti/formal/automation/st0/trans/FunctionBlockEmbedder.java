package edu.kit.iti.formal.automation.st0.trans;

import edu.kit.iti.formal.automation.st.ast.*;
import edu.kit.iti.formal.automation.st.util.AstCopyVisitor;

import java.util.function.Function;

/**
 * @author weigla
 * @date 26.06.2014
 */
public class FunctionBlockEmbedder extends AstCopyVisitor {
    private final String instanceName;
    private final StatementList toEmbedd;
    private Function<String, String> renameVariable;

    public FunctionBlockEmbedder(String instanceName, StatementList embeddable, Function<String, String> rename) {
        this.instanceName = instanceName;
        toEmbedd = embeddable;
        renameVariable = rename;
    }

    @Override
    public Object visit(SymbolicReference symbolicReference) {
        if (instanceName.equals(symbolicReference.getIdentifier())) {
		if(symbolicReference.getSub() != null) {
			String field = ((SymbolicReference) symbolicReference.getSub()).getIdentifier();
			SymbolicReference s = new SymbolicReference(instanceName + "$" + field);
			return s;
		}
        }
        return super.visit(symbolicReference);
    }

    @Override
    public Object visit(StatementList statements) {
        StatementList r = new StatementList();
        for (Statement s : statements) {
            Object visit = s.visit(this);
            if (visit instanceof StatementList) {
                r.addAll((StatementList) visit);
            } else {
                r.add((Statement) visit);
            }
        }
        return r;
    }

    @Override
    public Object visit(FunctionCallStatement functionCallStatement) {
        FunctionCall call = functionCallStatement.getFunctionCall();
        if (instanceName.equals(call.getFunctionName())) {
            StatementList sl = new StatementList();
            for (FunctionCall.Parameter p : call.getParameters()) {
                if (!p.isOutput()) {
                    String name = renameVariable.apply(p.getName());

                    AssignmentStatement assign = new AssignmentStatement(
                            new SymbolicReference(name, null),
                            p.getExpression()
                    );
                    sl.add(assign);
                }
            }
            sl.addAll(toEmbedd);

            for (FunctionCall.Parameter p : call.getParameters()) {
                if (p.isOutput()) {
                    String name = renameVariable.apply(p.getName());

                    AssignmentStatement assign = new AssignmentStatement(
                            (Reference) p.getExpression(),
                            new SymbolicReference(name, null)
                    );
                    sl.add(assign);
                }
            }

            return sl;
        } else {
            return super.visit(functionCallStatement);
        }
    }

    public StatementList embedd(StatementList into) {
        return (StatementList) into.visit(this);
    }
}
