package edu.kit.iti.formal.automation.apps;

import edu.kit.iti.formal.automation.sfclang.SFCLangPrinter;
import edu.kit.iti.formal.automation.sfclang.ast.SFCDeclaration;
import edu.kit.iti.formal.automation.sfclang.antlr.SFCLangLexer;
import edu.kit.iti.formal.automation.sfclang.antlr.SFCLangParser;
import edu.kit.iti.formal.automation.sfclang.antlr.SFCLangParser.Start_sfcContext;
import org.antlr.v4.runtime.ANTLRFileStream;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CommonTokenStream;

import java.io.IOException;

public class SFCExample {

	public static void main(String[] args) throws IOException {
		String filename = "example.sfc";
		if (args.length == 2) {
			filename = args[1];
		}

		CharStream stream = new ANTLRFileStream(filename);
		SFCLangLexer lexer = new SFCLangLexer(stream);
		SFCLangParser parser = new SFCLangParser(new CommonTokenStream(lexer));
		
		for (int i = 0; i < 2; i++) {
			Start_sfcContext sfccontext = parser.start_sfc();
			SFCDeclaration a = sfccontext.ast;

			System.out.println(SFCLangPrinter.print(a));
			
		}
	}

}
