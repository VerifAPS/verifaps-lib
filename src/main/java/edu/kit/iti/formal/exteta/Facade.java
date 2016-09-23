package edu.kit.iti.formal.exteta;

import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.util.List;

import javax.xml.bind.*;

import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.CommonTokenStream;

import edu.kit.formal.exteta.schema.ExtendedTestTableType;
import edu.kit.iti.formal.automation.parser.IEC61131Lexer;
import edu.kit.iti.formal.automation.parser.IEC61131Parser;
import edu.kit.iti.formal.automation.parser.IEC61131Parser.StartContext;
import edu.kit.iti.formal.automation.sfclang.SFCLangFactory;
import edu.kit.iti.formal.automation.sfclang.Utils;
import edu.kit.iti.formal.automation.sfclang.ast.SFCDeclaration;
import edu.kit.iti.formal.automation.st.ast.TopLevelElement;

public class Facade {
	public static ExtendedTestTableType readTable(String filename) throws JAXBException {
		File file = new File(filename);
		@SuppressWarnings("restriction")
		JAXBContext jc = JAXBContext.newInstance(ExtendedTestTableType.class);
		Unmarshaller jaxbUnmarshaller = jc.createUnmarshaller();
		return (ExtendedTestTableType) jaxbUnmarshaller.unmarshal(file);
	}

	public static List<TopLevelElement> readProgram(String optionValue) throws IOException {
		IEC61131Lexer lexer = new IEC61131Lexer(new ANTLRInputStream(new FileReader(optionValue)));
		CommonTokenStream cts = new CommonTokenStream(lexer);
		IEC61131Parser parser = new IEC61131Parser(cts);
		return parser.start().ast;
	}
}
