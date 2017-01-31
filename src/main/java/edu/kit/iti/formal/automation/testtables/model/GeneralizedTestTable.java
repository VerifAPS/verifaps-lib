package edu.kit.iti.formal.automation.testtables.model;

/*-
 * #%L
 * geteta
 * %%
 * Copyright (C) 2016 Alexander Weigl
 * %%
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */

import edu.kit.iti.formal.automation.st.ast.FunctionDeclaration;
import edu.kit.iti.formal.automation.st.ast.TopLevelElement;
import edu.kit.iti.formal.automation.testtables.io.IOFacade;
import edu.kit.iti.formal.automation.testtables.model.options.PropertyInitializer;
import edu.kit.iti.formal.automation.testtables.model.options.TableOptions;
import edu.kit.iti.formal.automation.testtables.schema.ConstraintVariable;
import edu.kit.iti.formal.automation.testtables.schema.IoVariable;
import edu.kit.iti.formal.automation.testtables.schema.Variable;
import edu.kit.iti.formal.smv.ast.SMVExpr;
import edu.kit.iti.formal.smv.ast.SVariable;

import java.util.*;

/**
 * @author Alexander Weigl
 * @version 2
 */
public class GeneralizedTestTable {
    private final LinkedHashMap<String, IoVariable> ioVariables = new LinkedHashMap<>();
    private final Map<String, ConstraintVariable> constraintVariables = new HashMap<>();
    private final Map<String, SVariable> variableMap = new HashMap<>();
    private final Properties properties = new Properties(System.getProperties());
    private final Map<String, FunctionDeclaration> functions = new HashMap<>();
    private final Map<SVariable, Integer> references = new HashMap<>();
    private Region region;
    private TableOptions options = null;
    private String name;

    public TableOptions getOptions() {
        if(options==null) {
            options = new TableOptions();
            PropertyInitializer.initialize(options, properties);
        }
        return options;
    }

    public GeneralizedTestTable setOptions(TableOptions options) {
        this.options = options;
        return this;
    }

    public Map<String, IoVariable> getIoVariables() {
        return ioVariables;
    }

    public Map<String, ConstraintVariable> getConstraintVariable() {
        return constraintVariables;
    }

    public Region getRegion() {
        return region;
    }

    public void setRegion(Region region) {
        this.region = region;
    }

    public SVariable getSMVVariable(String text) {
        variableMap.computeIfAbsent(text,
                (k) -> IOFacade.asSMVVariable(getVariable(k)));
        return variableMap.get(text);
    }

    private Variable getVariable(String text) {
        IoVariable a = ioVariables.get(text);
        ConstraintVariable b = constraintVariables.get(text);

        if(a!=null && b!=null)
            throw new IllegalStateException("constraint and io variable have the same name.");

        if (a != null)
            return a;
        else
            return b;
    }

    public void add(IoVariable v) {
        ioVariables.put(v.getName(), v);
    }

    public void add(ConstraintVariable v) {
        constraintVariables.put(v.getName(), v);
    }

    public void addOption(String key, String value) {
        properties.put(key, value);
        options = null; // reset options
    }

    public void addFunctions(List<TopLevelElement> file) {
        for (TopLevelElement e : file) {
            functions.put(e.getBlockName(), (FunctionDeclaration) e);
        }
    }

    public String getName() {
        return name;
    }

    public void setName(String name) {
        this.name = name;
    }

    public IoVariable getIoVariables(int i) {
        int k = 0;
        for (IoVariable v : ioVariables.values()) {
            if (k++ == i) return v;
        }
        return null;
    }

    public Map<SVariable, Integer> getReferences() {
        return references;
    }

    public SMVExpr getReference(SVariable columnVariable, int i) {
        if (i == 0) {
            return columnVariable;
        } else {
            SReference ref = new SReference(i, columnVariable);
            int max = Math.max(references.getOrDefault(columnVariable, i), i);
            references.put(columnVariable, max);
            return ref.asVariable();
        }
    }
}
