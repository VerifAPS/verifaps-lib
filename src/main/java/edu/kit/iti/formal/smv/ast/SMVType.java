package edu.kit.iti.formal.smv.ast;

import java.util.List;

public class SMVType {
	public static final SMVType BOOLEAN = new SMVType(GroundDataType.BOOLEAN);

	public GroundDataType base;

	public SMVType() {
	}

	public SMVType(GroundDataType b) {
		base = b;
	}

	public static SMVType infer(List<SMVType> list) {
		//TODO
		return null;
	}

	public static SMVType infer(SMVType a, SMVType b) {
		//TODO
		return null;
	}

	public static class SMVTypeWithWidth extends SMVType {
		int width;

		public SMVTypeWithWidth(GroundDataType dt, int i) {
			super(dt);
			width = i;
		}
	}

	public static class EnumType extends SMVType {
		List<String> values;

		public EnumType(List<String> id) {
			values = id;
		}

		public SLiteral valueOf(String value) {
			SLiteral l = super.valueOf(value);
			if (!values.contains(l.value)) {
				throw new IllegalArgumentException();
			}
			return l;
		}
	}

	public static SMVType unsigned(int i) {
		return new SMVTypeWithWidth(GroundDataType.UNSIGNED_WORD, i);
	}

	public static SMVType signed(int i) {
		return new SMVTypeWithWidth(GroundDataType.SIGNED_WORD, i);
	}

	public SLiteral valueOf(String value) {
		SLiteral l = new SLiteral();
		l.dataType = this;
		l.value = base.parse(value);
		return l;
	}

	public String format(Object value) {
		return base.format(value);
	}

}
