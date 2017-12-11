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

import com.google.common.collect.Streams;
import de.tudresden.inf.lat.jsexp.Sexp;
import de.tudresden.inf.lat.jsexp.SexpParserException;
import lombok.*;

import java.util.HashMap;
import java.util.Map;
import java.util.TreeMap;
import java.util.stream.Stream;

import static de.tudresden.inf.lat.jsexp.SexpFactory.newAtomicSexp;
import static de.tudresden.inf.lat.jsexp.SexpFactory.newNonAtomicSexp;

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

    /* for struct support
    private String stateDataTypeName = "program-state";
    private String inputDataTypeName = "program-input";
    */

    private Map<String, Sexp> inputDataTypes = new HashMap<>();
    private Map<String, Sexp> stateDataTypes = new HashMap<>();
    private Map<String, Sexp> initPredicates = new TreeMap<>();
    private Map<String, Sexp> nextPredicates = new TreeMap<>();

    private String initFuncName = "init";
    private String nextFuncName = "next";

    /**
     * adds the given arguments in the map into the given sexps.
     *
     * @param dt
     */
    private static Stream<Sexp> createSortSexp(String prefix, Map<String, Sexp> dt) {
        return dt.entrySet().stream()
                .map(entry -> {
                    Sexp s = newNonAtomicSexp();
                    s.add(newAtomicSexp(prefix + entry.getKey()));
                    s.add(entry.getValue());
                    return s;
                });
    }

    public Sexp getInitFunction() throws SexpParserException {
        Sexp func = newNonAtomicSexp();
        func.add(newAtomicSexp(DEFINE_FUNCTION));
        func.add(newAtomicSexp(initFuncName));
        func.add(toSexp(createSortSexp(STATE_NAME, stateDataTypes)));
        func.add(newAtomicSexp(SMT_BOOLEAN));
        func.add(getInitBody());
        return func;
    }

    private Sexp toSexp(Stream<Sexp> sortSexp) {
        Sexp list = newNonAtomicSexp();
        sortSexp.forEach(list::add);
        return list;
    }

    protected Sexp getInitBody() {
        Sexp body = newNonAtomicSexp();
        body.add(newAtomicSexp("and"));
        initPredicates.forEach((name, pred) -> {
            Sexp eq = newNonAtomicSexp();
            eq.add(newAtomicSexp("="));
            eq.add(newAtomicSexp(STATE_NAME + newAtomicSexp(name)));
            eq.add(pred);
            body.add(eq);
        });
        return body;
    }

    public Sexp getNextFunction() throws SexpParserException {
        Sexp func = newNonAtomicSexp();
        func.add(newAtomicSexp(DEFINE_FUNCTION));
        func.add(newAtomicSexp(nextFuncName));

        Stream<Sexp> s = createSortSexp(STATE_NAME, stateDataTypes);
        Stream<Sexp> i = createSortSexp(STATE_NAME, inputDataTypes);
        Stream<Sexp> t = createSortSexp(NEW_STATE_NAME, stateDataTypes);
        Sexp args = toSexp(Streams.concat(s, i, t));
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
            eq.add(newAtomicSexp(NEW_STATE_NAME + name));
            eq.add(pred);
            body.add(eq);
        });
        return body;
    }

    /*
    public Sexp getStateDataType() throws SexpParserException {
        return createRecord(stateDataTypeName, stateDataTypes);
    }

    public Sexp getInputDataType() throws SexpParserException {
        return createRecord(getInputDataTypeName(), inputDataTypes);
    }
    */

    public Stream<Sexp> getDefineSteps(String prefix, String suffix) {
        return Streams.concat(
                getDefineInputTypes(prefix, suffix),
                getDefineStateTypes(prefix, suffix)
        );
    }

    public Stream<Sexp> getDefineStateTypes(String prefix, String suffix) {
        return stateDataTypes.entrySet().stream()
                .map(e -> createDefineConst(prefix + e.getKey() + suffix, e.getValue()));
    }

    public Stream<Sexp> getDefineInputTypes(String prefix, String suffix) {
        return inputDataTypes.entrySet().stream()
                .map(e -> createDefineConst(prefix + e.getKey() + suffix, e.getValue()));
    }

    private Sexp createDefineConst(String name, Sexp sort) {
        Sexp s = newNonAtomicSexp();
        s.add(newAtomicSexp("declare-const"));
        s.add(newAtomicSexp(name));
        s.add(sort);
        return s;
    }

    /**
     * @return
     */
    public String getPreamble() {
        StringBuilder sb = new StringBuilder();
        sb.append("(set-logic QF_BV)\n");
        sb.append(
                "(define-fun <> ((a Bool) (b Bool)) Bool\n" +
                        "  (not (= a b)))\n");

        for (int i = 1; i <= 64; i++) {
            sb.append(String.format("(define-fun <> ((a (_ BitVec %d)) (b (_ BitVec %d))) Bool (not (= a b)))\n", i, i ));
        }


        try {
            Sexp init = getInitFunction();
            Sexp next = getNextFunction();
            sb.append(init.toIndentedString()).append("\n\n");
            sb.append(next.toIndentedString()).append("\n\n");
        } catch (SexpParserException e) {
            e.printStackTrace();
        }
        return sb.toString();
    }

    /**
     * @return
     */
    public String getStepDefinition(boolean withInput, String suffix) {
        StringBuilder sb = new StringBuilder();
        Stream<Sexp> init = getDefineInputTypes("", suffix);
        Stream<Sexp> next = getDefineStateTypes("", suffix);

        Stream<Sexp> vars = withInput ? Stream.concat(init, next) : next;

        vars.forEach(sexp -> {
            sb.append(sexp.toIndentedString())
                    .append("\n\n");
        });
        return sb.toString();
    }

    public Sexp getAssertInit(String suffix) {
        Sexp asser = newNonAtomicSexp();
        asser.add(newAtomicSexp("assert"));
        Sexp app = newNonAtomicSexp();
        asser.add(app);
        app.add(newAtomicSexp(initFuncName));
        stateDataTypes.keySet().forEach(name -> {
            app.add(newAtomicSexp(name + suffix));
        });
        return asser;
    }

    public Sexp getAssertNext(String previousSuffix, String nextSuffix) {
        Sexp asser = newNonAtomicSexp();
        asser.add(newAtomicSexp("assert"));
        Sexp app = newNonAtomicSexp();
        app.add(newAtomicSexp(nextFuncName));
        asser.add(app);
        stateDataTypes.keySet().forEach(name -> {
            app.add(newAtomicSexp(name + previousSuffix));
        });


        inputDataTypes.keySet().forEach(name -> {
            app.add(newAtomicSexp(name + previousSuffix));
        });

        stateDataTypes.keySet().forEach(name -> {
            app.add(newAtomicSexp(name + nextSuffix));
        });

        return asser;
    }


}
