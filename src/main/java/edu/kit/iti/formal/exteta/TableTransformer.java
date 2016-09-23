package edu.kit.iti.formal.exteta;

import edu.kit.formal.exteta.schema.ExtendedTestTableType;
import edu.kit.iti.formal.smv.ast.Module;

public class TableTransformer {

	private ExtendedTestTableType table;

	private Module module = new Module();
	
	public TableTransformer(ExtendedTestTableType table) {
		this.table = table;	
	}
	
	
	public Module transform() {
		module.name = "testtable";
		
		
		
		
		
		
		
		return module;
	}
	
}
