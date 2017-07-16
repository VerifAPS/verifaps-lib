package edu.kit.iti.formal.automation.testtables.builder;

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

import edu.kit.iti.formal.automation.testtables.StateReachability;
import edu.kit.iti.formal.automation.testtables.model.GeneralizedTestTable;
import edu.kit.iti.formal.automation.testtables.model.TableModule;
import edu.kit.iti.formal.smv.ast.SMVModule;
import edu.kit.iti.formal.smv.ast.SMVType;
import edu.kit.iti.formal.smv.ast.SVariable;

import java.util.Collection;
import java.util.LinkedList;
import java.util.List;
import java.util.function.Consumer;

public class TableTransformation {
    public static final String ERROR_STATE_IDENTIFIER = "___$ERROR$STATE";
    private final StateReachability reachable;
    private List<Consumer<TableTransformation>> transformers = new LinkedList<>();
    private GeneralizedTestTable gtt;
    private TableModule mt = new TableModule();
    private SVariable errorState = new SVariable(ERROR_STATE_IDENTIFIER, SMVType.BOOLEAN);
    private List<SMVModule> helper = new LinkedList<>();
    private SMVType superEnumType;

    public TableTransformation(GeneralizedTestTable table, SMVType superEnumType) {
        this.gtt = table;
        reachable = new StateReachability(table);
        this.superEnumType = superEnumType;
        init();
    }

    private void init() {
        transformers.clear();
        transformers.add(new NameSetterTransformer());
        transformers.add(new ModuleParameterTransformer());
        transformers.add(new StatesTransformer());
        transformers.add(new ConstraintVariableTransformer());
        transformers.add(new BackwardsReferencesTransformer());
        transformers.add(new LTLSpecTransformer());

        switch (gtt.getOptions().getMode()) {
            case CONFORMANCE:
                transformers.add(new ConformanceInvariantTransformer());
                break;
            case CONCRETE_TABLE:
                transformers.add(new ConcreteTableInvariantTransformer());
                break;
            case INPUT_SEQUENCE_EXISTS:
                transformers.add(new InputSequenceInvariantTransformer());
                break;
        }
    }

    public SMVModule transform() {
        transformers.forEach(a -> a.accept(this));
        return mt;
    }

    public Collection<SMVModule> getHelperModules() {
        return helper;
    }

    public TableModule getTableModule() {
        return mt;
    }

    public GeneralizedTestTable getTestTable() {
        return gtt;
    }

    public StateReachability getReachable() {
        return reachable;
    }

    public SVariable getErrorState() {
        return errorState;
    }

    public SMVType getSuperEnumType() {
        return superEnumType;
    }
}
