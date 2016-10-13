package edu.kit.iti.formal.exteta.model;

import java.util.ArrayList;
import java.util.List;

import edu.kit.formal.exteta.schema.VariableType;

public class GeneralizedTestTable {
	List<VariableType> variables = new ArrayList<>();
	List<Step> steps = new ArrayList<>();

	public List<VariableType> getVariables() {
		return variables;
	}

	public void setVariables(List<VariableType> variables) {
		this.variables = variables;
	}

	public List<Step> getSteps() {
		return steps;
	}

	public void setSteps(List<Step> steps) {
		this.steps = steps;
	}

	public void addStep(Step s) {
		steps.add(s);
		
	}

}
