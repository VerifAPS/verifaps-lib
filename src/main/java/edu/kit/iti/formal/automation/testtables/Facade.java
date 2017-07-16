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

import edu.kit.iti.formal.automation.IEC61131Facade;
import edu.kit.iti.formal.automation.datatypes.Any;
import edu.kit.iti.formal.automation.datatypes.AnyInt;
import edu.kit.iti.formal.automation.datatypes.DataTypes;
import edu.kit.iti.formal.automation.scope.GlobalScope;
import edu.kit.iti.formal.automation.st.ast.*;
import edu.kit.iti.formal.automation.st.util.AstVisitor;
import edu.kit.iti.formal.automation.testtables.io.TableReader;
import edu.kit.iti.formal.automation.testtables.io.xmv.NuXMVAdapter;
import edu.kit.iti.formal.automation.testtables.model.GeneralizedTestTable;
import edu.kit.iti.formal.automation.testtables.model.SReference;
import edu.kit.iti.formal.automation.testtables.model.VerificationTechnique;
import edu.kit.iti.formal.automation.testtables.model.options.TableOptions;
import edu.kit.iti.formal.automation.testtables.schema.DataType;
import edu.kit.iti.formal.smv.ast.SMVModule;
import edu.kit.iti.formal.smv.ast.SMVType;
import edu.kit.iti.formal.smv.ast.SVariable;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.Token;

import javax.xml.bind.JAXBException;
import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;

public class Facade {
    public static GeneralizedTestTable readTable(String filename) throws JAXBException {
        TableReader tr = new TableReader(new File(filename));
        tr.run();
        return tr.getProduct();
    }

    public static TopLevelElements readProgram(String optionValue) throws IOException {
        TopLevelElements a = IEC61131Facade.file(CharStreams.fromFileName(optionValue));
        IEC61131Facade.resolveDataTypes(a);
        resolveEnumsAndSetInts(a);
        return a;
    }

    private static void resolveEnumsAndSetInts(TopLevelElements a) {
        AstVisitor<Object> astVisitor = new AstVisitor<Object>() {
            public GlobalScope global;

            @Override
            public Object visit(ProgramDeclaration decl) {
                this.global = decl.getLocalScope().getGlobalScope();
                return super.visit(decl);
            }

            @Override
            public Object visit(VariableDeclaration declaration) {
                if (declaration.getDataType() instanceof AnyInt) {
                    declaration.setDataType(DataTypes.INT);
                    if(declaration.getInit()!=null && declaration.getInit() instanceof Literal) {
                        Literal l = (Literal) declaration.getInit();
                        l.setDataType(DataTypes.INT);
                    }
                }
                return declaration;
            }

            @Override
            public Object visit(Literal literal) {
                if (!literal.isDataTypeExplicit() && literal.getDataType() instanceof AnyInt) {
                    literal.setDataTypeExplicit(true);
                    literal.setDataType(DataTypes.INT);
                } else {
                    if (literal.getDataType() == null) {
                        String dt = literal.getDataTypeName();
                        if (dt != null && !dt.isEmpty()) {
                            Any a = global.resolveDataType(dt);
                            literal.setDataType(a);
                        }
                    }
                }
                return literal;
            }
        };
        a.accept(astVisitor);
    }

    public static DelayModuleBuilder delay(SReference ref) {
        DelayModuleBuilder dmb = new DelayModuleBuilder(ref.getVariable(),
                ref.getCycles());
        return dmb;
    }


    public static SMVModule glue(SMVModule modTable, SMVModule modCode, TableOptions options) {
        BinaryModelGluer mg = new BinaryModelGluer(options, modTable, modCode);
        mg.run();
        return mg.getProduct();
    }

    public static boolean runNuXMV(String tableFilename,
                                   VerificationTechnique technique, SMVModule... modules) {
        return runNuXMV(tableFilename, Arrays.asList(modules), technique);
    }

    public static String getHistoryName(SVariable variable, int cycles) {
        return getHistoryName(variable) + "._$" + cycles;
    }

    public static String getHistoryName(SVariable variable) {
        return variable.getName() + "__history";
    }

    public static boolean runNuXMV(String tableFilename,
                                   List<SMVModule> modules, VerificationTechnique vt) {
        NuXMVAdapter adapter = new NuXMVAdapter(new File(tableFilename), modules);
        adapter.setTechnique(vt);
        adapter.run();
        return adapter.isVerified();
    }

    public static SMVType createSuperEnum(TopLevelElements code) {
        SuperEnumCreator sec = new SuperEnumCreator();
        code.accept(sec);
        return sec.getType();
    }

    private static class SuperEnumCreator extends AstVisitor<Void> {
        private SMVType.EnumType type = new SMVType.EnumType(new ArrayList<>());

        public SMVType getType() {
            return type;
        }

        @Override
        public Void visit(EnumerationTypeDeclaration etd) {
            type.getValues().addAll(etd.getAllowedValues().stream().map(Token::getText).collect(Collectors.toList()));
            return null;
        }
    }
}
