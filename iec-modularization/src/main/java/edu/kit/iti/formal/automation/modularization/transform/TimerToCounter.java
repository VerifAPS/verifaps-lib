package edu.kit.iti.formal.automation.modularization.transform;

/*-
 * #%L
 * iec-modularization
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

import edu.kit.iti.formal.automation.datatypes.Any;
import edu.kit.iti.formal.automation.datatypes.AnyBit;
import edu.kit.iti.formal.automation.datatypes.DataTypes;
import edu.kit.iti.formal.automation.modularization.StatementListModifier;
import edu.kit.iti.formal.automation.operators.Operators;
import edu.kit.iti.formal.automation.scope.Scope;
import edu.kit.iti.formal.automation.st.ast.*;

import java.util.HashSet;
import java.util.Map;
import java.util.Set;

// Must be invoked before data types are resolved, as the TON causes an
// exception otherwise
public class TimerToCounter extends StatementListModifier {

    private final Set<String> _tonInstances = new HashSet<>();

    public TimerToCounter() {
        super(false);
    }

    private void _addVariable(
            final VariableDeclaration src,
            final String name,
            final String typeName,
            final Scope dst) {

        final TypeDeclaration type = new SimpleTypeDeclaration();

        type.setBaseTypeName(typeName);
        type.setTypeName(typeName);

        dst.add(new VariableDeclaration(
                src.getName() + "$" + name,
                VariableDeclaration.LOCAL,
                type));
    }

    private Literal _createLiteral(
            final Any type,
            final String value) {

        final Literal literal = new Literal(type, value);
        literal.setDataTypeExplicit(true);
        return literal;
    }

    @Override
    public final Object visit(final Scope localScope) {

        final Set<VariableDeclaration> variables =
                new HashSet<>(localScope.asMap().values());
        final Map<String, VariableDeclaration> varScope =
                localScope.asMap();

        for (VariableDeclaration i : variables) {

            if (!i.getDataTypeName().equals("TON")) continue;

            _tonInstances.add(i.getName());
            varScope.remove(i.getName());

            _addVariable(i, "IN", "BOOL", localScope);
            _addVariable(i, "PT", "INT", localScope);
            _addVariable(i, "Q", "BOOL", localScope);
            _addVariable(i, "ET", "INT", localScope);
        }

        return null;
    }

    @Override
    public final Object visit(final InvocationStatement fbCallStmt) {

        final String name = fbCallStmt.getCalleeName();

        if (_tonInstances.contains(name)) {

            final SymbolicReference in = new SymbolicReference(name + "$IN");
            final SymbolicReference pt = new SymbolicReference(name + "$PT");
            final SymbolicReference q = new SymbolicReference(name + "$Q");
            final SymbolicReference et = new SymbolicReference(name + "$ET");

            final IfStatement isInTrue = new IfStatement();
            final StatementList isInTrueThen = new StatementList();
            final StatementList isInTrueElse = isInTrue.getElseBranch();
            final IfStatement isElapsed = new IfStatement();
            final StatementList isElapsedThen = new StatementList();

            isInTrue.addGuardedCommand(in, isInTrueThen);

            isInTrueThen.add(new AssignmentStatement(
                    q, new BinaryExpression(et, pt, Operators.EQUALS)));
            isInTrueThen.add(isElapsed);

            isElapsed.addGuardedCommand(
                    new UnaryExpression(Operators.NOT, q), isElapsedThen);

            isElapsedThen.add(new AssignmentStatement(et, new BinaryExpression(
                    et, _createLiteral(DataTypes.INT, "1"),
                    Operators.ADD)));

            isInTrueElse.add(new AssignmentStatement(
                    q, _createLiteral(AnyBit.BOOL, "FALSE")));
            isInTrueElse.add(new AssignmentStatement(
                    et, _createLiteral(DataTypes.INT, "0")));

            _addToCurrentList(isInTrue);

        } else {
            _addToCurrentList(fbCallStmt);
        }
        return null;
    }
}
