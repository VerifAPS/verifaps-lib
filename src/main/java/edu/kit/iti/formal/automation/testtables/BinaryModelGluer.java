package edu.kit.iti.formal.automation.testtables;

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

import edu.kit.iti.formal.automation.testtables.exception.SpecificationInterfaceMisMatchException;
import edu.kit.iti.formal.smv.ast.SMVModule;
import edu.kit.iti.formal.smv.ast.SMVModuleImpl;
import edu.kit.iti.formal.smv.ast.SMVType;
import edu.kit.iti.formal.smv.ast.SVariable;

import java.util.List;
import java.util.stream.Collectors;

/**
 * @author Alexander Weigl
 * @version 1 (13.12.16)
 */
public class BinaryModelGluer implements Runnable {
    public static final String TABLE_MODULE = "table";
    public static final String CODE_MODULE = "code";
    public static final String MAIN_MODULE = "main";
    private final SMVModule code;
    private final SMVModule table;
    private SMVModuleImpl product = new SMVModuleImpl();

    public BinaryModelGluer(SMVModule modTable, SMVModule modCode) {
        table = modTable;
        code = modCode;
    }


    public SMVModule getProduct() {
        return product;
    }

    @Override
    public void run() {
        product.setName(MAIN_MODULE);
        code.getModuleParameter().forEach(product.getInputVars()::add);

        product.getStateVars().add(new SVariable(
                CODE_MODULE,
                new SMVType.Module(code.getName(),
                        code.getModuleParameter())));

        List<SVariable> taP =
                table.getModuleParameter().stream().map(
                        v -> {
                            if (code.getModuleParameter().contains(v)) {
                                return v;
                            } else {
                                if (!code.getStateVars().contains(v)) {
                                    throw new SpecificationInterfaceMisMatchException(code, v);
                                }
                                return new SVariable(CODE_MODULE +"."+ v,
                                        v.getSMVType());
                            }
                        }
                ).collect(Collectors.toList());
        product.getStateVars().add(new SVariable(TABLE_MODULE,
                new SMVType.Module(table.getName(), taP)));
    }
}
