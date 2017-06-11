package edu.kit.iti.formal.smv.parser;

/*-
 * #%L
 * smv-model
 * %%
 * Copyright (C) 2017 Alexander Weigl
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

import edu.kit.iti.formal.smv.ast.*;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

/**
 * @author Alexander Weigl
 * @version 1 (10.06.17)
 */
public class SMVTransformToAST extends SMVBaseVisitor<Object> {
    private SMVModuleImpl lastModule;

    @Override
    public List<SMVModule> visitModules(SMVParser.ModulesContext ctx) {
        List<SMVModule> moduleDeclarations = new ArrayList<>();
        ctx.module().forEach(c -> moduleDeclarations.add((SMVModule) c.accept(this)));
        return moduleDeclarations;
    }

    @Override
    public SMVModuleImpl visitModule(SMVParser.ModuleContext ctx) {
        SMVModuleImpl module = new SMVModuleImpl();
        module.setName(ctx.name.getText());
        ctx.params.forEach(fpctx ->
                module.getModuleParameter().add(
                        SVariable.create(fpctx.getText()).with(null)));

        lastModule = module;
        ctx.moduleElement().forEach(c -> c.accept(this));
        return module;
    }

    @Override
    public Object visitModuleElement(SMVParser.ModuleElementContext ctx) {
        return ctx.getChild(0).accept(this);
    }

    @Override
    public Object visitVariableDeclaration(SMVParser.VariableDeclarationContext ctx) {
        ctx.varBody().forEach(varBody ->
                lastModule.getStateVars().add(
                        (SVariable) varBody.accept(this)));
        return lastModule.getStateVars();
    }

    @Override
    public Object visitIVariableDeclaration(SMVParser.IVariableDeclarationContext ctx) {
        ctx.varBody().forEach(varBody ->
                lastModule.getInputVars().add(
                        (SVariable) varBody.accept(this)));
        return lastModule.getStateVars();
    }

    @Override
    public Object visitFrozenVariableDeclaration(SMVParser.FrozenVariableDeclarationContext ctx) {
        ctx.varBody().forEach(varBody ->
                lastModule.getFrozenVars().add(
                        (SVariable) varBody.accept(this)));
        return lastModule.getStateVars();
    }

    @Override
    public SVariable visitVarBody(SMVParser.VarBodyContext ctx) {
        SVariable sVariable = new SVariable();
        sVariable.setName(ctx.name.getText());
        sVariable.setDatatype((SMVType) ctx.type().accept(this));
        return sVariable;
    }

    @Override
    public Object visitDefineBody(SMVParser.DefineBodyContext ctx) {
        lastModule.getDefinitions().put(
                SVariable.create(ctx.var.getText()).with(null),
                (SMVExpr) ctx.expr().accept(this));
        return null;
    }

    @Override
    public Object visitConstantsDeclaration(SMVParser.ConstantsDeclarationContext ctx) {
        throw new IllegalStateException("not supported");
    }

    @Override
    public Object visitVarBodyAssign(SMVParser.VarBodyAssignContext ctx) {
        return super.visitVarBodyAssign(ctx);
    }

    @Override
    public Object visitInitBody(SMVParser.InitBodyContext ctx) {
        lastModule.getInitAssignments().add(
                new SAssignment(
                        SVariable.create(ctx.var.getText()).with(null),
                        (SMVExpr) ctx.expr().accept(this)
                ));
        return null;
    }

    @Override
    public Object visitNextBody(SMVParser.NextBodyContext ctx) {
        lastModule.getNextAssignments().add(
                new SAssignment(
                        SVariable.create(ctx.var.getText()).with(null),
                        (SMVExpr) ctx.expr().accept(this)
                ));
        return null;
    }

    @Override
    public Object visitFairnessConstraint(SMVParser.FairnessConstraintContext ctx) {
        return super.visitFairnessConstraint(ctx);
    }

    @Override
    public Object visitPslSpecification(SMVParser.PslSpecificationContext ctx) {
        return super.visitPslSpecification(ctx);
    }

    @Override
    public Object visitInvarSpecification(SMVParser.InvarSpecificationContext ctx) {
        lastModule.getInvarSpec().add(
                (SMVExpr) ctx.expr().accept(this)
        );
        return null;
    }

    @Override
    public Object visitCtlSpecification(SMVParser.CtlSpecificationContext ctx) {
        lastModule.getCTLSpec().add(
                (SMVExpr) ctx.expr().accept(this)
        );
        return null;
    }

    @Override
    public Object visitIsaDeclaration(SMVParser.IsaDeclarationContext ctx) {
        return super.visitIsaDeclaration(ctx);
    }

    @Override
    public Object visitLtlSpecification(SMVParser.LtlSpecificationContext ctx) {
        lastModule.getLTLSpec().add((SMVExpr) ctx.expr().accept(this));
        return null;
    }


    @Override
    public SMVType visitType(SMVParser.TypeContext ctx) {
        if (ctx.moduleType() != null) {
            return (SMVType) ctx.moduleType().accept(this);
        } else {
            return (SMVType) ctx.simpleType().accept(this);
        }
    }

    @Override
    public SMVType visitBooleanType(SMVParser.BooleanTypeContext ctx) {
        return SMVType.BOOLEAN;
    }

    @Override
    public Object visitWordType(SMVParser.WordTypeContext ctx) {
        return super.visitWordType(ctx);
    }

    @Override
    public Object visitSignedType(SMVParser.SignedTypeContext ctx) {
        return new SMVType.SMVTypeWithWidth(GroundDataType.SIGNED_WORD,
                Integer.parseInt(ctx.bits.getText()));
    }

    @Override
    public Object visitUnsignedType(SMVParser.UnsignedTypeContext ctx) {
        return new SMVType.SMVTypeWithWidth(GroundDataType.UNSIGNED_WORD,
                Integer.parseInt(ctx.bits.getText()));
    }

    @Override
    public Object visitEnumType(SMVParser.EnumTypeContext ctx) {
        List<String> ids =
                ctx.expr()
                        .stream().map(ectx -> ectx.getText())
                        .collect(Collectors.toList());
        SMVType.EnumType e = new SMVType.EnumType(ids);
        return e;
    }

    @Override
    public Object visitIntervalType(SMVParser.IntervalTypeContext ctx) {
        throw new IllegalStateException("not supported");
//        return super.visitIntervalType(ctx);
    }

    @Override
    public Object visitArrayType(SMVParser.ArrayTypeContext ctx) {
        throw new IllegalStateException("not supported");
        //  return super.visitArrayType(ctx);
    }

    @Override
    public Object visitModuleTypeSimple(SMVParser.ModuleTypeSimpleContext ctx) {
        List<SMVExpr> parameters = ctx.stateExpr().stream()
                .map(se -> (SMVExpr) se.accept(this))
                .collect(Collectors.toList());
        SMVType.Module m = new SMVType.Module(ctx.mod.getText(), parameters);
        return m;
    }

    @Override
    public SMVExpr visitStateExpr(SMVParser.StateExprContext ctx) {
        if (ctx.unaryop != null) {
            return new SUnaryExpression(
                    ctx.unaryop.getText().equals("!")
                            ? SUnaryOperator.NEGATE
                            : SUnaryOperator.MINUS,
                    (SMVExpr) ctx.stateExpr(0).accept(this)
            );
        }

        if (ctx.terminalAtom() != null) {
            return (SMVExpr) ctx.terminalAtom().accept(this);
        }

        return new SBinaryExpression(
                (SMVExpr) ctx.stateExpr(0).accept(this),
                SBinaryOperator.findBySymbol(ctx.op.getText()),
                (SMVExpr) ctx.stateExpr(1).accept(this)
        );
    }

    @Override
    public SMVExpr visitParen(SMVParser.ParenContext ctx) {
        return (SMVExpr) ctx.stateExpr().accept(this);
    }

    @Override
    public Object visitSetExpr(SMVParser.SetExprContext ctx) {
        throw new IllegalStateException("not supported");
//        return super.visitSetExpr(ctx);
    }

    @Override
    public Object visitWordValue(SMVParser.WordValueContext ctx) {
        String[] p = ctx.getText().split("_");
        GroundDataType gdt = p[0].charAt(1) == 's'
                ? GroundDataType.SIGNED_WORD
                : GroundDataType.UNSIGNED_WORD;

        int bits = Integer.parseInt(p[0].substring(3));

        return SLiteral.create(new BigInteger(p[1])).as(bits, gdt);
        //return super.visitWordValue(ctx);
    }

    @Override
    public Object visitRangeExpr(SMVParser.RangeExprContext ctx) {
        throw new IllegalStateException("not supported");
        //return super.visitRangeExpr(ctx);
    }

    @Override
    public Object visitCasesExpr(SMVParser.CasesExprContext ctx) {
        SCaseExpression e = new SCaseExpression();
        for (SMVParser.CaseBranchContext a : ctx.caseBranch()) {
            SMVExpr cond = (SMVExpr) a.cond.accept(this);
            SMVExpr val = (SMVExpr) a.val.accept(this);
            e.add(cond, val);
        }
        return e;
    }


    @Override
    public SLiteral visitTrueExpr(SMVParser.TrueExprContext ctx) {
        return SLiteral.TRUE;
    }

    @Override
    public SLiteral visitFalseExpr(SMVParser.FalseExprContext ctx) {
        return SLiteral.FALSE;
    }

    @Override
    public Object visitDefineDeclaration(SMVParser.DefineDeclarationContext ctx) {
        return super.visitDefineDeclaration(ctx);
    }

    @Override
    public Object visitAssignConstraint(SMVParser.AssignConstraintContext ctx) {
        return super.visitAssignConstraint(ctx);
    }

    @Override
    public Object visitAssignBody(SMVParser.AssignBodyContext ctx) {
        return super.visitAssignBody(ctx);
    }

    @Override
    public Object visitTrans(SMVParser.TransContext ctx) {
        return super.visitTrans(ctx);
    }

    @Override
    public Object visitInit(SMVParser.InitContext ctx) {
        return super.visitInit(ctx);
    }

    @Override
    public Object visitInvar(SMVParser.InvarContext ctx) {
        return super.visitInvar(ctx);
    }

    @Override
    public Object visitVariableID(SMVParser.VariableIDContext ctx) {
        return super.visitVariableID(ctx);
    }

    @Override
    public Object visitModuleTypeProcess(SMVParser.ModuleTypeProcessContext ctx) {
        throw new IllegalStateException("not supported");
    }

    @Override
    public Object visitCtlUnaryExpr(SMVParser.CtlUnaryExprContext ctx) {
        return new SQuantified(STemporalOperator.valueOf(ctx.op),
                (SMVExpr) ctx.expr().accept(this));
    }

    @Override
    public Object visitLtlBinaryOp(SMVParser.LtlBinaryOpContext ctx) {
        return new SQuantified(STemporalOperator.valueOf(ctx.op),
                (SMVExpr) ctx.expr(0).accept(this),
                (SMVExpr) ctx.expr(1).accept(this));
    }

    @Override
    public Object visitCtlBinaryOp(SMVParser.CtlBinaryOpContext ctx) {
        return new SQuantified(STemporalOperator.valueOf(ctx.op),
                (SMVExpr) ctx.expr(0).accept(this),
                (SMVExpr) ctx.expr(1).accept(this));
    }

    @Override
    public Object visitLtlUnaryOp(SMVParser.LtlUnaryOpContext ctx) {
        return new SQuantified(
                STemporalOperator.valueOf(ctx.op),
                (SMVExpr) ctx.expr().accept(this)
        );
    }

    @Override
    public Object visitFunctionExpr(SMVParser.FunctionExprContext ctx) {
        List<SMVExpr> exprs = getSMVExprs(ctx);
        return new SFunction(ctx.func.getText(), exprs);
    }

    private List<SMVExpr> getSMVExprs(SMVParser.FunctionExprContext ctx) {
        return ctx.stateExpr().stream().map(
                c -> (SMVExpr) c.accept(this)
        ).collect(Collectors.toList());
    }

    @Override
    public Object visitCasesExprAtom(SMVParser.CasesExprAtomContext ctx) {
        return super.visitCasesExprAtom(ctx);
    }

    @Override
    public Object visitVariableAccess(SMVParser.VariableAccessContext ctx) {
        return SVariable.create(ctx.getText()).with(null);
    }

    @Override
    public Object visitArrayAccess(SMVParser.ArrayAccessContext ctx) {
        throw new IllegalStateException("not supported");
    }

    @Override
    public Object visitVariableDotted(SMVParser.VariableDottedContext ctx) {
        throw new IllegalStateException("not supported");
    }

    @Override
    public Object visitNumberExpr(SMVParser.NumberExprContext ctx) {
        return new SLiteral(SMVType.INT,
                new BigInteger(ctx.value.getText()));
    }

    @Override
    public Object visitCaseBranch(SMVParser.CaseBranchContext ctx) {
        return super.visitCaseBranch(ctx);
    }
}