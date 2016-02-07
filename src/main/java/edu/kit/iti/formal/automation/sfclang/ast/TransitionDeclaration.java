package edu.kit.iti.formal.automation.sfclang.ast;

import edu.kit.iti.formal.automation.ast.Expression;
import edu.kit.iti.formal.automation.sfclang.SFCAstVisitor;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

public class TransitionDeclaration {
	Expression guard;
	Set<String> from = new HashSet<>();
	Set<String> to = new HashSet<>();

	public Expression getGuard() {
		return guard;
	}

	public void setGuard(Expression guard) {
		this.guard = guard;
	}

	public Set<String> getFrom() {
		return from;
	}

	public void setFrom(Set<String> from) {
		this.from = from;
	}

	public Set<String> getTo() {
		return to;
	}

	public void setTo(Set<String> to) {
		this.to = to;
	}

	public <T> T visit(SFCAstVisitor<T> v) {
		return v.visit(this);
	}

	public void setFrom(List<String> ast) {
		setFrom(new HashSet<>(ast));
	}

	public void setTo(List<String> ast) {
		setTo(new HashSet<>(ast));
	}
}
