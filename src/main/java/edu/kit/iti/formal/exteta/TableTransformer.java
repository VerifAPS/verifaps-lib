package edu.kit.iti.formal.exteta;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import javax.xml.bind.JAXBElement;


import static edu.kit.iti.formal.smv.BExpressionBuilder.*;
import edu.kit.formal.exteta.schema.DataTypeType;
import edu.kit.formal.exteta.schema.ExtendedTestTableType;
import edu.kit.formal.exteta.schema.VariableType;
import edu.kit.formal.exteta.schema.VariablesType;
import edu.kit.iti.formal.smv.ast.DataType;
import edu.kit.iti.formal.smv.ast.Expression;
import edu.kit.iti.formal.smv.ast.GroundDataType;
import edu.kit.iti.formal.smv.ast.Literal;
import edu.kit.iti.formal.smv.ast.Module;
import edu.kit.iti.formal.smv.ast.Variable;
import edu.kit.iti.formal.smv.model.State;
import edu.kit.iti.formal.smv.model.TStateSystem;
import edu.kit.iti.formal.smv.model.Transition;

public class TableTransformer {

	private ExtendedTestTableType table;

	private Module module = new Module();

	public TableTransformer(ExtendedTestTableType table) {
		this.table = table;
	}

	public Module transform() {
		TStateSystem tss = new TStateSystem();
		tss.name = "table";

		List<VariableType> vt = table.getVariables().getVariable();
		List<Variable> v = vt.stream().map(TableTransformer::toVar).collect(Collectors.toList());
		tss.statevars.addAll(v);

		List<State> lines = new ArrayList<>();
		int lineno = 0;

		for (TimeFrameType tf : table.getTimeFrames().getTimeFrame()) {
			State s = new State();
			s.id = "" + lineno;
			lineno++;
			s.assignments = buildAssignments(tf.getConstOrCaptureOrExpr(), v);
			lines.add(s);
		}

		State sfinal = new State("final");

		for (int i = 0; i < lines.size(); i++) {
			TimeEntry te = parse(table.getTimeFrames().getTimeFrame().get(i).getTimeEntry());
			State c = lines.get(i);
			State n = i < lines.size() - 1 ? lines.get(i + 1) : sfinal;

			if (te.oneStep()) {
				c.next.add(new Transition().from(c).to(n).on(Literal.TRUE));

			}
		}

		tss.init = lines.get(0);

		return tss.asModule();
	}

	class TimeEntry {
		int start, stop;

		public boolean oneStep() {
			return start == 1 && stop == 1;
		}

		public boolean fixedStep() {
			return start == stop;
		}

		public boolean finiteInterval() {
			return stop != -1;
		}
	}

	private TimeEntry parse(String timeEntry) {
		TimeEntry te = new TimeEntry();
		if (timeEntry.matches("\\d+")) {
			int i = Integer.parseInt(timeEntry);
			te.start = te.stop = i;
		} else {
			// String[] q = timeEntry.replace('[', ' ').replace(']', '
			// ').split(' ');
			throw new IllegalArgumentException("TODO");
			// TODO
		}
		return te;
	}

	private Map<Variable, Expression> buildAssignments(List<JAXBElement<String>> list, List<Variable> vars) {
		Map<Variable, Expression> map = new HashMap<>();
		for (int i = 0; i < vars.size(); i++) {
			Variable v = vars.get(i);
			JAXBElement<String> e = list.get(i);

			switch (e.getName().getLocalPart()) {
			case "const":
				map.put(v, expr(v).equal().to(v.getDataType().valueOf(e.getValue())).get());
				break;
			default:
				throw new IllegalArgumentException();
				/*
				 * case "dontcare": break; case "expr": break; case "rel":
				 * break; case "capture": break;
				 */
			}
		}

		return map;
	}

	public static Variable toVar(VariableType v) {
		DataType dt = convert(v.getDataType());
		return new Variable(v.getName(), dt);
	}

	private static DataType convert(DataTypeType dataType) {
		switch (dataType) {
		case BOOLEAN:
			return DataType.BOOLEAN;
		case BYTE:
			return DataType.unsigned(8);
		case INT:
			return DataType.signed(16);
		case SINT:
			return DataType.signed(8);
		case WORD:
			return DataType.unsigned(16);

		}
		return null;
	}

}
