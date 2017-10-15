package edu.kit.iti.formal.automation.smt;

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

    private static Sexp getArgsFor(Map<String, Sexp> dt) {
        Sexp args = newNonAtomicSexp();
        createSortSexp(dt, args);
        return args;
    }

    /**
     * adds the given arguments in the map into the given sexps.
     *
     * @param dt
     * @param args
     */
    private static void createSortSexp(Map<String, Sexp> dt, Sexp args) {
        dt.forEach((name, datatype) -> {
                    Sexp arg = newNonAtomicSexp();
                    arg.add(newAtomicSexp(name));
                    arg.add(datatype);
                    args.add(arg);
                }
        );
    }

    public static Sexp createRecord(String name, Map<String, Sexp> dataTypes) {
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
        Sexp dt = newNonAtomicSexp();
        dt.add(newAtomicSexp(DECLARE_DATATYPES));
        dt.add(newNonAtomicSexp());
        Sexp defs = newNonAtomicSexp();
        Sexp def = newNonAtomicSexp();
        Sexp con = newNonAtomicSexp();
        defs.add(def);
        def.add(con);
        def.add(newAtomicSexp(name));
        con.add(newAtomicSexp("mk-" + name));
        createSortSexp(dataTypes, con);
        return dt;
    }

    public Sexp getInitFunction(String name) throws SexpParserException {
        Sexp func = newNonAtomicSexp();
        func.add(newAtomicSexp(DEFINE_FUNCTION));
        func.add(newAtomicSexp(name));
        Sexp args = SexpFactory.parse(String.format("((%s %s))",
                NEW_STATE_NAME, stateDataTypeName));
        func.add(args);
        func.add(newAtomicSexp(SMT_BOOLEAN));
        func.add(getInitBody());
        return func;
    }

    protected Sexp getInitBody() {
        Sexp body = newNonAtomicSexp();
        body.add(newAtomicSexp("and"));
        initPredicates.forEach((name, pred) -> {
            body.add(pred);
        });
        return body;
    }

    public Sexp getNextFunction(String name) throws SexpParserException {
        Sexp func = newNonAtomicSexp();
        func.add(newAtomicSexp(DEFINE_FUNCTION));
        func.add(newAtomicSexp(name));
        Sexp args = SexpFactory.parse(String.format("((%s %s) (%s %s) (%s %s))",
                STATE_NAME, stateDataTypeName,
                INPUT_NAME, inputDataTypes,
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

    public Sexp getStateDataType() {
        return createRecord(stateDataTypeName, stateDataTypes);
    }

    public Sexp getInputDataType() {
        return createRecord(getInputDataTypeName(), inputDataTypes);
    }

    public String getSMT(String initFuncName, String initNextName) {
        try {
            Sexp dataType = getStateDataType();
            Sexp inputType = getInputDataType();
            Sexp init = getInitFunction(initFuncName);
            Sexp next = getNextFunction(initNextName);

            return dataType.toIndentedString() +
                    inputType.toIndentedString() +
                    init.toIndentedString() +
                    next.toIndentedString();
        } catch (SexpParserException e) {
            e.printStackTrace();
        }
        return null;
    }
}
