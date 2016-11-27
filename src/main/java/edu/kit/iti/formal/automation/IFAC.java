package edu.kit.iti.formal.automation;

import java.io.File;
import java.io.IOException;
import edu.kit.iti.formal.automation.st.ast.TopLevelElements;
import edu.kit.iti.formal.automation.st0.ST0Factory;

public class IFAC {
	public static void main(String[] args) throws IOException {
		File input = new File(args[0]);
		Console.info("Processing: %s", input);
		//TopLevelElements ast = Transformer.parse(input);
		//TopLevelElements st0ast = ST0Factory.simplify(ast);

		
		//ast.visit(new StructuredTextPrinter());
		
		// String name = fInput.getName().replace("_Final.xml", "");

		//ModuleDeclaration md = SymbexFactory.toCaseExpression(st0ast);
		//String s = md.toString();
		//System.out.println(s.toString());

	}

}
