package edu.kit.iti.formal.smv.ast;

public enum GroundDataType {
	SIGNED_WORD(true), UNSIGNED_WORD(true), INT, FLOAT, BOOLEAN;
	
	public boolean hasWidth;
	GroundDataType() {this(false);}
	GroundDataType(boolean has_width){
		hasWidth = has_width;
	}
	
}
