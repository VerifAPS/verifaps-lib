package edu.kit.iti.formal.smv.model;

import edu.kit.iti.formal.smv.ast.SMVExpr;
import edu.kit.iti.formal.smv.ast.SLiteral;

public class Transition {
	public State outgoing;
	public State incoming;

	public SMVExpr guard = SLiteral.TRUE;

	public Transition from(State s) {
		outgoing = s;
		return this;
	}

	public Transition to(State n) {
		incoming = n;
		return this;
	}

	public Transition on(SMVExpr g) {
		guard = g;
		return this;
	}

}
