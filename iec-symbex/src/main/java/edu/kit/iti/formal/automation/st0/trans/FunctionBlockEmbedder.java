package edu.kit.iti.formal.automation.st0.trans;

/*-
 * #%L
 * iec61131lang
 * %%
 * Copyright (C) 2017 Alexander Weigl
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

import edu.kit.iti.formal.automation.st.ast.*;
import edu.kit.iti.formal.automation.st.util.AstMutableVisitor;
import lombok.Builder;
import lombok.Getter;
import lombok.val;

import java.util.HashMap;
import java.util.Map;
import java.util.function.Function;

/**
 * @author Alexander Weigl (26.06.2014)
 * @version 1
 */
@Builder
public class FunctionBlockEmbedder extends AstMutableVisitor {
    private final String instanceName;
    private final StatementList toEmbedd;
    @Getter
    private final Map<String, StatementList> actions = new HashMap<>();
    private final Function<String, String> renameVariable;

    @Override
    public Object visit(SymbolicReference symbolicReference) {
        if (instanceName.equals(symbolicReference.getIdentifier())) {
            if (symbolicReference.getSub() != null) {
                String field = symbolicReference.getSub().getIdentifier();
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
            Object visit = s.accept(this);
            if (visit == null) {
                throw new IllegalArgumentException("got null for " + s.getNodeName());
            }
            if (visit instanceof StatementList) {
                r.addAll((StatementList) visit);
            } else {
                r.add((Statement) visit);
            }
        }
        return r;
    }

    @Override
    public Object visit(InvocationStatement fbc) {
        val call = fbc.getCallee();
        if (!instanceName.equals(call.getIdentifier())) {
            return super.visit(fbc); // I am not caring about this instance.
        }

        // rewrite input parameters as assignments
        // f(a:=2) ==> f$a:=2; f()
        StatementList sl = new StatementList();
        fbc.getInputParameters().forEach(in -> {
            String internalName = renameVariable.apply(in.getName());
            sl.add(new AssignmentStatement(
                    new SymbolicReference(internalName),
                    in.getExpression()
            ));
        });

        sl.add(CommentStatement.single("Call of %s:%s", instanceName, fbc.getCalleeName()));
        if (call.getSub() == null) {//insert main statement block
            sl.addAll(this.toEmbedd);
        } else {
            String actionName = call.getSub().getIdentifier();
            if (actions.containsKey(actionName)) {
                sl.addAll(actions.get(actionName));
            } else {
                sl.add(CommentStatement.single("//ERROR: COULD NOT FIND ACTION %s.%s",
                        instanceName, actionName));
            }
        }

        //rewrite output variables as trailing assignments.
        fbc.getOutputParameters().forEach(p -> {
            String name = renameVariable.apply(p.getName());
            AssignmentStatement assign = new AssignmentStatement(
                    (Reference) p.getExpression(),
                    new SymbolicReference(name)
            );
            sl.add(assign);
        });
        sl.add(CommentStatement.single("End of call"));
        return sl;
    }

    public StatementList embedd(StatementList into) {
        return (StatementList) into.accept(this);
    }
}
