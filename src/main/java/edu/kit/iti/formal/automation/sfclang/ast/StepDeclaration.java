package edu.kit.iti.formal.automation.sfclang.ast;

import edu.kit.iti.formal.automation.sfclang.SFCAstVisitor;

import java.util.LinkedList;
import java.util.List;

/**
 *
 *
 */
public class StepDeclaration {
	String name;
	List<String> onExit = new LinkedList<>();
	List<String> onActive = new LinkedList<>();
	List<String> onEntry = new LinkedList<>();
	private boolean initial;

	public String getName() {
		return name;
	}

	public void setName(String name) {
		this.name = name;
	}

	public List<String> getOnExit() {
		return onExit;
	}

	public void setOnExit(List<String> on_exit) {
		this.onExit = on_exit;
	}

	public List<String> getOnActive() {
		return onActive;
	}

	public void setOnActive(List<String> on_active) {
		this.onActive = on_active;
	}

	public List<String> getOnEntry() {
		return onEntry;
	}

	public void setOnEntry(List<String> on_entry) {
		this.onEntry = on_entry;
	}

	public void push(String eventType, String actionName) {
		switch (eventType) {
		case "entry":
			onEntry.add(actionName);
			break;
		case "exit":
			onExit.add(actionName);
			break;
		case "active":
			onActive.add(actionName);
			break;
		default:
			throw new IllegalArgumentException();
		}
	}

	public <T> T visit(SFCAstVisitor<T> v)
	{
		return v.visit(this);
	}

	public boolean isInitialStep() {
		return name.equals("Init");
	}

	public void setInitial(boolean initial) {
		this.initial = initial;
	}
}
