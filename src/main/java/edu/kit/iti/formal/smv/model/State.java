package edu.kit.iti.formal.smv.model;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import edu.kit.iti.formal.smv.ast.SMVExpr;
import edu.kit.iti.formal.smv.ast.SVariable;

public class State {
	public State() {
	}

	public State(String string) {
		id = string;
	}

	public String id;
	public Map<SVariable, SMVExpr> assignments = new HashMap<>();
	public List<Transition> next = new ArrayList<>();	
}
