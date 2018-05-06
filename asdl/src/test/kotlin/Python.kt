import edu.kit.iti.formal.asdl.ADSL
import org.junit.Test

/**
 *
 * @author Alexander Weigl
 * @version 1 (15.04.18)
 */

class PythonTest : ADSL() {
    val python = module {
        name = "Python"

        val mod = group("TopLevel") {
            leaf("Module",
                    many("stmt", "body"),
                    optional("String", "docstring"))
            leaf("Interactive", "stmt* body")
            leaf("Expression", "expr body")
            leaf("Suite", "stmt* body")
        }

        val stmt = group("Statement") {
            leaf("FunctionDef", "identifier name, arguments args, stmt* body, expr* decorator_list, expr? returns, string? docstring")
            leaf("AsyncFunctionDef", "identifier name, arguments args, stmt* body, expr* decorator_list, expr? returns,  string? docstring")
            leaf("ClassDef", "identifier name, expr* bases, keyword* keywords, stmt* body, expr* decorator_list, string? docstring")
            leaf("Return", "expr? value")
            leaf("Delete", "expr* targets")
            leaf("Assign", "expr* targets, expr value")
            leaf("AugAssign", "expr target, operator op, expr value")
            leaf("AnnAssign", "expr target, expr annotation, expr? value, int simple")
            leaf("For", "expr target, expr iter, stmt* body, stmt* orelse")
            leaf("AsyncFor", "expr target, expr iter, stmt* body, stmt* orelse")
            leaf("While", "expr test, stmt* body, stmt* orelse")
            leaf("If", "expr test, stmt* body, stmt* orelse")
            leaf("With", "withitem* items, stmt* body")
            leaf("AsyncWith", "withitem* items, stmt* body")
            leaf("Raise", "expr? exc, expr? cause")
            leaf("Try", "stmt* body, excepthandler* handlers, stmt* orelse, stmt* finalbody")
            leaf("Assert", "expr test, expr? msg")
            leaf("Import", "alias* names")
            leaf("ImportFrom", "identifier? module, alias* names, int? level")
            leaf("Global", "identifier* names")
            leaf("Nonlocal", "identifier* names")
            leaf("Expr", "expr value")
            leaf("Pass")
            leaf("Break")
            leaf("Continue")
        }

        val expr = group("expr") {
            leaf("BoolOp", "boolop op, expr* values")
            leaf("BinOp", "expr left, operator op, expr right")
            leaf("UnaryOp", "unaryop op, expr operand")
            leaf("Lambda", "arguments args, expr body")
            leaf("IfExp", "expr test, expr body, expr orelse")
            leaf("Dict", "expr* keys, expr* values")
            leaf("Set", "expr* elts")
            leaf("ListComp", "expr elt, comprehension* generators")
            leaf("SetComp", "expr elt, comprehension* generators")
            leaf("DictComp", "expr key, expr value, comprehension* generators")
            leaf("GeneratorExp", "expr elt, comprehension* generators")
            leaf("Await", "expr value")
            leaf("Yield", "expr? value")
            leaf("YieldFrom", "expr value")
            leaf("Compare", "expr left, cmpop* ops, expr* comparators")
            leaf("Call", "expr func, expr* args, keyword* keywords")
            leaf("Num", "object n")
            leaf("Str", "string s")
            leaf("FormattedValue", "expr value, int? conversion, expr? format_spec")
            leaf("JoinedStr", "expr* values")
            leaf("Bytes", "bytes s")
            leaf("NameConstant", "singleton value")
            leaf("Ellipsis")
            leaf("Constant", "constant value")
            leaf("Attribute", "expr value, identifier attr, expr_context ctx")
            leaf("Subscript", "expr value, slice slice, expr_context ctx")
            leaf("Starred", "expr value, expr_context ctx")
            leaf("Name", "identifier id, expr_context ctx")
            leaf("List", "expr* elts, expr_context ctx")
            leaf("Tuple", "expr* elts, expr_context ctx")
        }
//    expr_context = Load , Store, Del, AugLoad, AugStore, Param

        val slice = group("slice") {
            leaf("Slice", "expr? lower, expr? upper, expr? step")
            leaf("ExtSlice", "slice* dims")
            leaf("Index", "expr value")
        }

        val boolop = group("boolop") {
            leaf("And");
            leaf("Or")
        }

        val operator = group("operator") {
            leaf("Add"); leaf("Sub"); leaf("Mult"); leaf("MatMult"); leaf("Div"); leaf("Mod"); leaf("Pow"); leaf("LShift");
            leaf("RShift"); leaf("BitOr"); leaf("BitXor"); leaf("BitAnd"); leaf("FloorDiv")
        }

        val unaryop = group("unaryop") {
            leaf("Invert"); leaf("Not"); leaf("UAdd"); leaf("USub")
        }

        val cmpop = group("cmpop") {
            leaf("Eq"); leaf("NotEq"); leaf("Lt"); leaf("LtE"); leaf("Gt"); leaf("GtE"); leaf("Is"); leaf("IsNot"); leaf("In");
            leaf("NotIn")
        }
        val comprehension = leaf("comprehension", "expr target, expr iter, expr* ifs, int is_async")
        val excepthandler = leaf("ExceptHandler", "expr? type, identifier? name, stmt* body")


/*arguments = ("arg* args, arg? vararg, arg* kwonlyargs, expr* kw_defaults, arg? kwarg, expr* defaults")
arg = (identifier arg, expr? annotation)
keyword = (identifier? arg, expr value)
alias = (identifier name, identifier? asname)
withitem = (expr context_expr, expr? optional_vars)*/

    }

    @Test
    fun test() {
        println(python)
    }
}