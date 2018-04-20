package edu.kit.iti.formal.automation.smt;

/*-
 * #%L
 * cexplorer
 * %%
 * Copyright (C) 2016 - 2017 Alexander Weigl
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

import de.tudresden.inf.lat.jsexp.Sexp;
import edu.kit.iti.formal.smv.SMVAstVisitor;
import edu.kit.iti.formal.smv.ast.*;
import lombok.Getter;
import lombok.RequiredArgsConstructor;
import lombok.Setter;

import javax.annotation.Nonnull;
import java.util.List;
import java.util.stream.Collectors;

import static de.tudresden.inf.lat.jsexp.SexpFactory.newAtomicSexp;
import static de.tudresden.inf.lat.jsexp.SexpFactory.newNonAtomicSexp;

/**
 * @author Alexander Weigl
 * @version 1 (27.01.17), 2 (15.10.17)
 */
@RequiredArgsConstructor
public class SSA2SMT implements Runnable {
    @Getter
    private final SMVModule input;

    @Getter
    private final SMTProgram product = new SMTProgram();

    @Getter
    @Setter
    private S2SDataTypeTranslator dtTranslator = new DefaultS2STranslator();

    @Getter
    @Setter
    private S2SFunctionTranslator fnTranslator = new DefaultS2SFunctionTranslator();


    @Override
    public void run() {
        Smv2SMTVisitor v = new Smv2SMTVisitor();

        //rewrite initial assignments
        input.getInit().forEach(a -> product.getInitPredicates().put(a.target.getName(),
                a.expr.accept(v)));

        //rewrite next assignments
        input.getNext().forEach(a -> {
            product.getNextPredicates().put(a.target.getName(),
                    a.expr.accept(v));
        });

        //define state values
        input.getStateVars().forEach(var -> {
                    product.getStateDataTypes()
                            .put(var.getName(),
                                    dtTranslator.translate(var.getDatatype()));
                }
        );

        //define input values
        input.getModuleParameters().forEach(var -> {
                    product.getInputDataTypes()
                            .put(var.getName(),
                                    dtTranslator.translate(var.getDatatype()));
                }
        );
    }


    class Smv2SMTVisitor implements SMVAstVisitor<Sexp> {
        @Override
        public Sexp visit(SMVAst top) {
            throw new IllegalStateException("illegal AST node discovered!");
        }

        @Override
        public Sexp visit(SVariable v) {
            /*Sexp access = newNonAtomicSexp();
            access.add(newAtomicSexp(v.getName()));
            access.add(newAtomicSexp(SMTProgram.STATE_NAME));
            */
            return newAtomicSexp(SMTProgram.STATE_NAME + v.getName());
        }

        @Override
        public Sexp visit(SBinaryExpression be) {
            Sexp left = be.getLeft().accept(this);
            Sexp right = be.getRight().accept(this);
            Sexp op = fnTranslator.translateOperator(be.getOperator(),
                    be.getLeft().getSMVType(), be.getRight().getSMVType());

            Sexp call = newNonAtomicSexp();
            call.add(op);
            call.add(left);
            call.add(right);
            return call;
        }

        @Override
        public Sexp visit(SUnaryExpression ue) {
            Sexp right = ue.getExpr().accept(this);
            Sexp op = fnTranslator.translateOperator(ue.getOperator(), ue.getExpr().getSMVType());
            Sexp call = newNonAtomicSexp();
            call.add(op);
            call.add(right);
            return call;
        }

        @Override
        public Sexp visit(SLiteral l) {
            return dtTranslator.translate(l);
        }

        @Override
        public Sexp visit(SAssignment a) {
            throw new IllegalStateException("illegal AST node discovered!");
        }

        @Override
        public Sexp visit(SCaseExpression ce) {
            return ifThenElse(ce.getCases(), 0);
        }

        @Override
        public Sexp visit(SFunction func) {
            List<Sexp> args = func.getArguments().stream().map(arg -> arg.accept(this))
                    .collect(Collectors.toList());
            return fnTranslator.translateOperator(func, args);
        }

        @Override
        public Sexp visit(SMVModule smvModule) {
            throw new IllegalStateException("illegal AST node discovered!");
        }


        @Override
        public Sexp visit(SQuantified quantified) {
            throw new IllegalStateException("illegal AST node discovered! SQuantified not allowed in assignments");
        }

        @Nonnull
        private Sexp ifThenElse(final List<SCaseExpression.Case> cases, int n) {
            if (n >= cases.size()) {
                throw new IllegalArgumentException();
            }

            if (n == cases.size() - 1) {//last element
                // ignoring the last condition for well-definedness
                return cases.get(n).getThen().accept(this);
            }

            Sexp ite = newNonAtomicSexp();
            ite.add(newAtomicSexp("ite"));
            ite.add(cases.get(n).getCondition().accept(this));
            ite.add(cases.get(n).getThen().accept(this));
            ite.add(ifThenElse(cases, n + 1));
            return ite;
        }
    }
}
