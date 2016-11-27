package edu.kit.iti.formal.smv.ast;

import java.util.ArrayList;
import java.util.List;

import edu.kit.iti.formal.smv.SMVAstVisitor;

/************************************************************/
/**
 * 
 */
public class SMVModule extends SMVAst {
	/**
	 * 
	 */
	public List<SVariable> inputvars = new ArrayList<>();
	/**
	 * 
	 */
	public List<SVariable> statevars = new ArrayList<>();
	/**
	 * 
	 */
	public List<SVariable> frozenvars = new ArrayList<>();

	public List<SAssignment> init = new ArrayList<>();

	public List<SMVExpr> invariants = new ArrayList<>(), invariantspecs = new ArrayList<>(),
			ltlspec = new ArrayList<>(), ctlspec = new ArrayList<>();

	public List<SAssignment> next = new ArrayList<>();

	public String name;

	@Override
	public <T> T accept(SMVAstVisitor<T> visitor) {
		return visitor.visit(this);
	}

}
