package edu.kit.iti.formal.automation.smt;

/*-
 * #%L
 * iec-symbex
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

import de.tudresden.inf.lat.jsexp.Sexp;
import de.tudresden.inf.lat.jsexp.SexpFactory;
import de.tudresden.inf.lat.jsexp.SexpParserException;
import lombok.*;

import java.util.HashMap;
import java.util.Map;
import java.util.TreeMap;

import static de.tudresden.inf.lat.jsexp.SexpFactory.*;

/**
 * This class represents a reactive program in SMT formulas.
 * <p>
 * Additionally it provides some meta data over these function.
 * <p>
 * <p>
 * An SMT program consist out of three parts:
 * <ul>
 * <li>A predicate <em>init(X)</em> for valid initial states <em>X</em></li>
 * <li>A predicate <em>next(X,I,X')</em> for valid successor states</li>
 * <li>A description of states <em>X</em></li>
 * <li>A description of input values <em>I</em></li>
 * </ul>
 * </p>
 *
 * @author Alexander Weigl
 * @version 1 (15.10.17)
 */
@Data
@ToString
@EqualsAndHashCode
@AllArgsConstructor
@NoArgsConstructor
public class SMTProgram {
    public static final String NEW_STATE_NAME = "new";
    public static final String STATE_NAME = "old";
    public static final String INPUT_NAME = "input";

    public final static String DEFINE_FUNCTION = "define-fun";
    public static final String SMT_BOOLEAN = "Bool";

    public static final String DECLARE_DATATYPES = "declare-datatypes";

    private String stateDataTypeName = "program-state";
    private String inputDataTypeName = "program-input";

    private Map<String, Sexp> inputDataTypes = new HashMap<>();
    private Map<String, Sexp> stateDataTypes = new HashMap<>();
    private Map<String, Sexp> initPredicates = new TreeMap<>();
    private Map<String, Sexp> nextPredicates = new TreeMap<>();
    private Sexp inputDefinition;

    /**
     * adds the given arguments in the map into the given sexps.
     *
     * @param dt
     */
    private static String createSortSexp(Map<String, Sexp> dt) {
        return dt.entrySet().stream()
                .map(entry -> "(" + entry.getKey() + " " + entry.getValue() + ")")
                .reduce((a, b) -> a + " " + b)
                .orElse("");
    }

    public static Sexp createRecord(String name, Map<String, Sexp> dataTypes) throws SexpParserException {
        /*
         * <pre>
         * (declare-datatype () ( (state (constructor (name type) ...)))))
         * ^                    ^ ^      ^
         * | dt                 | |      | con
         *                      | | def
         *                      | defs
         * </pre>
         *
         */
        String s = String.format("(declare-datatypes () ( (%s (mk-%s %s))))",
                name, name, createSortSexp(dataTypes));
        return SexpFactory.parse(s);
    }

    public Sexp getInitFunction(String name) throws SexpParserException {
        Sexp func = newNonAtomicSexp();
        func.add(newAtomicSexp(DEFINE_FUNCTION));
        func.add(newAtomicSexp(name));
        Sexp args = SexpFactory.parse(String.format("((%s %s))",
                STATE_NAME, stateDataTypeName));
        func.add(args);
        func.add(newAtomicSexp(SMT_BOOLEAN));
        func.add(getInitBody());
        return func;
    }

    protected Sexp getInitBody() {
        Sexp body = newNonAtomicSexp();
        body.add(newAtomicSexp("and"));
        initPredicates.forEach((name, pred) -> {
            Sexp eq = newNonAtomicSexp();
            eq.add(newAtomicSexp("="));
            Sexp access = newNonAtomicSexp();
            access.add(newAtomicSexp(STATE_NAME));
            access.add(newAtomicSexp(name));
            eq.add(access);
            eq.add(pred);
            body.add(eq);
        });
        return body;
    }

    public Sexp getNextFunction(String name) throws SexpParserException {
        Sexp func = newNonAtomicSexp();
        func.add(newAtomicSexp(DEFINE_FUNCTION));
        func.add(newAtomicSexp(name));
        Sexp args = SexpFactory.parse(String.format("((%s %s) (%s %s) (%s %s))",
                STATE_NAME, stateDataTypeName,
                INPUT_NAME, inputDataTypeName,
                NEW_STATE_NAME, stateDataTypeName
        ));
        func.add(args);
        func.add(newAtomicSexp(SMT_BOOLEAN));
        func.add(getNextBody());
        return func;
    }

    protected Sexp getNextBody() throws SexpParserException {
        Sexp body = newNonAtomicSexp();
        body.add(newAtomicSexp("and"));
        nextPredicates.forEach((name, pred) -> {
            Sexp eq = newNonAtomicSexp();
            eq.add(newAtomicSexp("="));
            try {
                eq.add(parse(String.format("(%s %s)", NEW_STATE_NAME, name)));
            } catch (SexpParserException e) {
                e.printStackTrace();
            }
            eq.add(pred);
            body.add(eq);
        });
        return body;
    }

    public Sexp getStateDataType() throws SexpParserException {
        return createRecord(stateDataTypeName, stateDataTypes);
    }

    public Sexp getInputDataType() throws SexpParserException {
        return createRecord(getInputDataTypeName(), inputDataTypes);
    }

    public String getSMT(String initFuncName, String initNextName) {
        try {
            Sexp dataType = getStateDataType();
            Sexp inputType = getInputDataType();
            Sexp init = getInitFunction(initFuncName);
            Sexp next = getNextFunction(initNextName);

            return dataType.toIndentedString() + "\n\n" +
                    inputType.toIndentedString() + "\n\n" +
                    init.toIndentedString() + "\n\n" +
                    next.toIndentedString();
        } catch (SexpParserException e) {
            e.printStackTrace();
        }
        return null;
    }
}
