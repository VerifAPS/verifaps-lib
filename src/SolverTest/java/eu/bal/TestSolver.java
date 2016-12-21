package eu.bal;

import org.chocosolver.solver.Model;
import org.chocosolver.solver.variables.BoolVar;
import org.chocosolver.solver.variables.IntVar;
import org.chocosolver.solver.variables.Variable;

/**
 * Class for testing constraint solver
 * @author bal
 */
public class TestSolver {

	private Model model;
	
	public TestSolver() {
		model = new Model("Test Problem");
		// Create variables
		IntVar var1 = model.intVar("A", 1, 3); // A bounded to interval [1,3] --> All int vars must have a bounded domain
		IntVar var2 = model.intVar("B", new int[]{4,5});
		BoolVar var3 = model.boolVar("C");
		// Post constraints
		model.not(model.arithm(var1, "=", var2)).post();
		model.arithm(var2, "<", 5).post();
	}
	
	public void solve() {
		model.getSolver().solve();
		for (Variable var : model.getVars()) {
			System.out.println(var);
		}
	}
	
	public static void main(String[] args) {
		TestSolver solver = new TestSolver();
		solver.solve();
	}

}
