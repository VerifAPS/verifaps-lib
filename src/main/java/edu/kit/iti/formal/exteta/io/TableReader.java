package edu.kit.iti.formal.exteta.io;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;

import javax.xml.bind.JAXBContext;
import javax.xml.bind.JAXBElement;
import javax.xml.bind.JAXBException;
import javax.xml.bind.Unmarshaller;

import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.misc.ParseCancellationException;

import edu.kit.formal.exteta.schema.ExtendedTestTableType;
import edu.kit.formal.exteta.schema.ObjectFactory;
import edu.kit.formal.exteta.schema.StepType;
import edu.kit.formal.exteta.schema.VariableType;
import edu.kit.iti.formal.exteta.ExTeTa;
import edu.kit.iti.formal.exteta.grammar.CellExpressionLexer;
import edu.kit.iti.formal.exteta.grammar.CellExpressionParser;
import edu.kit.iti.formal.exteta.model.Expression;
import edu.kit.iti.formal.exteta.model.GeneralizedTestTable;
import edu.kit.iti.formal.exteta.model.Step;

public class TableReader {
	private File input;
	GeneralizedTestTable gtt = new GeneralizedTestTable();

	public TableReader(File input) {
		this.input = input;
	}

	public void run() throws JAXBException {
		if (ExTeTa.DEBUG) {
			System.out.format("read xml file %s%n", input);
		}

		@SuppressWarnings("restriction")
		JAXBContext jc = JAXBContext.newInstance(ObjectFactory.class);
		Unmarshaller jaxbUnmarshaller = jc.createUnmarshaller();
		JAXBElement<?> root = (JAXBElement<?>) jaxbUnmarshaller.unmarshal(input);
		ExtendedTestTableType xml = (ExtendedTestTableType) root.getValue();

		if (ExTeTa.DEBUG) {
			System.out.format("xml file successfully read", input);
		}

		translateVariables(xml);
		translateSteps(xml);
	}

	private void translateSteps(ExtendedTestTableType xml) {
		int stepNumber = 0;
		for (StepType step : xml.getSteps().getStep()) {
			stepNumber++;

			if (ExTeTa.DEBUG) {
				System.out.format("Step #%d%n", stepNumber);
			}

			if (step.getCell().size() != xml.getVariables().getVariable().size()) {
				System.err.format("The amount of cells does not match the number of variables in step #%d%n",
						stepNumber);
			}

			Step s = new Step();
			s.setDuration(parseDuration(step.getDuration()));
			for (int i = 0; i < step.getCell().size(); i++) {
				String cell = step.getCell().get(i);
				VariableType v = xml.getVariables().getVariable().get(i);
				try {
					Expression expr = parseExpression(cell);
					s.setConstraint(v, expr);

					if (ExTeTa.DEBUG) {
						System.out.format("\t%s => %s%n", v.getName(), expr);
					}
				} catch (ParseCancellationException e) {
					System.err.format("Syntax Error in step %d in cell %d (%s): %s%n", stepNumber, i, cell,
							e.getMessage());
				}
			}
			gtt.addStep(s);
		}
	}

	public static CellExpressionParser createParser(String input) {
		CellExpressionLexer lexer = new CellExpressionLexer(new ANTLRInputStream(input));
		lexer.removeErrorListeners();
		lexer.addErrorListener(ThrowingErrorListener.INSTANCE);

		CellExpressionParser parser = new CellExpressionParser(new CommonTokenStream(lexer));

		parser.removeErrorListeners();
		parser.addErrorListener(ThrowingErrorListener.INSTANCE);

		return parser;
	}

	private Expression parseExpression(String cell) {
		return createParser(cell).cell().ast;
	}

	private Expression parseDuration(String duration) {
		return createParser(duration).duration().ast;
	}

	private void translateVariables(ExtendedTestTableType xml) {
		if (ExTeTa.DEBUG) {
			System.out.format("%d variables found%n", xml.getVariables().getVariable().size());
			for (VariableType v : xml.getVariables().getVariable()) {
				System.out.format("\t %s : %s %n", v.getName(), v.getDataType());
			}
		}
		gtt.getVariables().addAll(xml.getVariables().getVariable());
	}

	public GeneralizedTestTable getProduct() {
		return gtt;
	}

}
