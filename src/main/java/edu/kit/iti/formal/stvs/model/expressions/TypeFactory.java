package stverificationstudio.expressions;

import java.util.Arrays;

public class TypeFactory {
	
	public static final TypeInt INT = new TypeInt();
	public static final TypeBool BOOL = new TypeBool();
	
	public static TypeEnum enumOfName(String name, String... values) {
		return new TypeEnum(name, Arrays.asList(values));
	}

}
