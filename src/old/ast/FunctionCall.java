package edu.kit.iti.formal.common.expression.ast;

import java.util.List;

public class FunctionCall extends Expr {

	public List<Expr> arguments;
	public String fnname;

	public FunctionCall(String text, List<Expr> args) {
		arguments = args;
		fnname = text;
	}

	@Override
	public <T> T accept(Visitor<T> visitor) {
		return visitor.visit(this);
	}

	public List<Expr> getArguments() {
		return arguments;
	}

	public void setArguments(List<Expr> arguments) {
		this.arguments = arguments;
	}

	public String getFunctionName() {
		return fnname;
	}

	public void setFunctionName(String fnname) {
		this.fnname = fnname;
	}

	@Override
	public List<Expr> getChildren() {
		return getArguments();
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((arguments == null) ? 0 : arguments.hashCode());
		result = prime * result + ((fnname == null) ? 0 : fnname.hashCode());
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		FunctionCall other = (FunctionCall) obj;
		if (arguments == null) {
			if (other.arguments != null)
				return false;
		} else if (!arguments.equals(other.arguments))
			return false;
		if (fnname == null) {
			if (other.fnname != null)
				return false;
		} else if (!fnname.equals(other.fnname))
			return false;
		return true;
	}

	@Override
	public int getPrecedence() {
		return 0;
	}

}
