package edu.kit.iti.formal.exteta.model;

import java.util.HashMap;
import java.util.Map;

import edu.kit.formal.exteta.schema.VariableType;

public class Step {
	private Expression duration;
	private Map<VariableType, Expression> constraints = new HashMap<>();

	public Step() {
	}
	
	
	public Expression getDuration() {
		return duration;
	}

	public void setDuration(Expression duration) {
		this.duration = duration;
	}

	public Map<VariableType, Expression> getConstraints() {
		return constraints;
	}

	public void setConstraints(Map<VariableType, Expression> constraints) {
		this.constraints = constraints;
	}

	public Expression setConstraint(VariableType v, Expression expr) {
		return constraints.put(v, expr);
	}

}
