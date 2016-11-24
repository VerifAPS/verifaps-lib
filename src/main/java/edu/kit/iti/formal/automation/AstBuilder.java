package edu.kit.iti.formal.automation;

import edu.kit.iti.formal.automation.parser.IEC61131Parser;
import edu.kit.iti.formal.automation.parser.IEC61131ParserBaseVisitor;
import edu.kit.iti.formal.automation.st.ast.Top;
import edu.kit.iti.formal.automation.st.ast.TopLevelElement;
import edu.kit.iti.formal.automation.st.ast.TopLevelElements;

/**
 * Created by weigl on 24.11.16.
 */
public class AstBuilder extends IEC61131ParserBaseVisitor<Top> {
    public TopLevelElements visitStart(IEC61131Parser.StartContext ctx) {
        TopLevelElements tle = new TopLevelElements();
        return tle;
    }

    @Override
    public Top visitLibrary_element_declaration(IEC61131Parser.Library_element_declarationContext ctx) {
        return super.visitLibrary_element_declaration(ctx);
    }

    @Override
    public Top visitLibrary_element_name(IEC61131Parser.Library_element_nameContext ctx) {
        return super.visitLibrary_element_name(ctx);
    }

    @Override
    public Top visitConstant(IEC61131Parser.ConstantContext ctx) {
        return super.visitConstant(ctx);
    }

    @Override
    public Top visitCast(IEC61131Parser.CastContext ctx) {
        return super.visitCast(ctx);
    }

    @Override
    public Top visitInteger(IEC61131Parser.IntegerContext ctx) {
        return super.visitInteger(ctx);
    }

    @Override
    public Top visitBits(IEC61131Parser.BitsContext ctx) {
        return super.visitBits(ctx);
    }

    @Override
    public Top visitReal(IEC61131Parser.RealContext ctx) {
        return super.visitReal(ctx);
    }

    @Override
    public Top visitString(IEC61131Parser.StringContext ctx) {
        return super.visitString(ctx);
    }

    @Override
    public Top visitTime(IEC61131Parser.TimeContext ctx) {
        return super.visitTime(ctx);
    }

    @Override
    public Top visitTimeofday(IEC61131Parser.TimeofdayContext ctx) {
        return super.visitTimeofday(ctx);
    }

    @Override
    public Top visitDate(IEC61131Parser.DateContext ctx) {
        return super.visitDate(ctx);
    }

    @Override
    public Top visitDatetime(IEC61131Parser.DatetimeContext ctx) {
        return super.visitDatetime(ctx);
    }

    @Override
    public Top visitData_type_name(IEC61131Parser.Data_type_nameContext ctx) {
        return super.visitData_type_name(ctx);
    }

    @Override
    public Top visitNon_generic_type_name(IEC61131Parser.Non_generic_type_nameContext ctx) {
        return super.visitNon_generic_type_name(ctx);
    }

    @Override
    public Top visitElementary_type_name(IEC61131Parser.Elementary_type_nameContext ctx) {
        return super.visitElementary_type_name(ctx);
    }

    @Override
    public Top visitNumeric_type_name(IEC61131Parser.Numeric_type_nameContext ctx) {
        return super.visitNumeric_type_name(ctx);
    }

    @Override
    public Top visitInteger_type_name(IEC61131Parser.Integer_type_nameContext ctx) {
        return super.visitInteger_type_name(ctx);
    }

    @Override
    public Top visitSigned_integer_type_name(IEC61131Parser.Signed_integer_type_nameContext ctx) {
        return super.visitSigned_integer_type_name(ctx);
    }

    @Override
    public Top visitUnsigned_integer_type_name(IEC61131Parser.Unsigned_integer_type_nameContext ctx) {
        return super.visitUnsigned_integer_type_name(ctx);
    }

    @Override
    public Top visitReal_type_name(IEC61131Parser.Real_type_nameContext ctx) {
        return super.visitReal_type_name(ctx);
    }

    @Override
    public Top visitDate_type_name(IEC61131Parser.Date_type_nameContext ctx) {
        return super.visitDate_type_name(ctx);
    }

    @Override
    public Top visitBit_string_type_name(IEC61131Parser.Bit_string_type_nameContext ctx) {
        return super.visitBit_string_type_name(ctx);
    }

    @Override
    public Top visitGeneric_type_name(IEC61131Parser.Generic_type_nameContext ctx) {
        return super.visitGeneric_type_name(ctx);
    }

    @Override
    public Top visitData_type_declaration(IEC61131Parser.Data_type_declarationContext ctx) {
        return super.visitData_type_declaration(ctx);
    }

    @Override
    public Top visitType_declaration(IEC61131Parser.Type_declarationContext ctx) {
        return super.visitType_declaration(ctx);
    }

    @Override
    public Top visitSimple_type_declaration(IEC61131Parser.Simple_type_declarationContext ctx) {
        return super.visitSimple_type_declaration(ctx);
    }

    @Override
    public Top visitSimple_spec_init(IEC61131Parser.Simple_spec_initContext ctx) {
        return super.visitSimple_spec_init(ctx);
    }

    @Override
    public Top visitSimple_specification(IEC61131Parser.Simple_specificationContext ctx) {
        return super.visitSimple_specification(ctx);
    }

    @Override
    public Top visitSubrange_type_declaration(IEC61131Parser.Subrange_type_declarationContext ctx) {
        return super.visitSubrange_type_declaration(ctx);
    }

    @Override
    public Top visitSubrange_spec_init(IEC61131Parser.Subrange_spec_initContext ctx) {
        return super.visitSubrange_spec_init(ctx);
    }

    @Override
    public Top visitSubrange_specification(IEC61131Parser.Subrange_specificationContext ctx) {
        return super.visitSubrange_specification(ctx);
    }

    @Override
    public Top visitSubrange(IEC61131Parser.SubrangeContext ctx) {
        return super.visitSubrange(ctx);
    }

    @Override
    public Top visitEnumerated_type_declaration(IEC61131Parser.Enumerated_type_declarationContext ctx) {
        return super.visitEnumerated_type_declaration(ctx);
    }

    @Override
    public Top visitEnumerated_specification(IEC61131Parser.Enumerated_specificationContext ctx) {
        return super.visitEnumerated_specification(ctx);
    }

    @Override
    public Top visitArray_type_declaration(IEC61131Parser.Array_type_declarationContext ctx) {
        return super.visitArray_type_declaration(ctx);
    }

    @Override
    public Top visitArray_spec_init(IEC61131Parser.Array_spec_initContext ctx) {
        return super.visitArray_spec_init(ctx);
    }

    @Override
    public Top visitArray_specification(IEC61131Parser.Array_specificationContext ctx) {
        return super.visitArray_specification(ctx);
    }

    @Override
    public Top visitArray_initialization(IEC61131Parser.Array_initializationContext ctx) {
        return super.visitArray_initialization(ctx);
    }

    @Override
    public Top visitArray_initial_elements(IEC61131Parser.Array_initial_elementsContext ctx) {
        return super.visitArray_initial_elements(ctx);
    }

    @Override
    public Top visitArray_initial_element(IEC61131Parser.Array_initial_elementContext ctx) {
        return super.visitArray_initial_element(ctx);
    }

    @Override
    public Top visitStructure_type_declaration(IEC61131Parser.Structure_type_declarationContext ctx) {
        return super.visitStructure_type_declaration(ctx);
    }

    @Override
    public Top visitStructure_specification(IEC61131Parser.Structure_specificationContext ctx) {
        return super.visitStructure_specification(ctx);
    }

    @Override
    public Top visitInitialized_structure(IEC61131Parser.Initialized_structureContext ctx) {
        return super.visitInitialized_structure(ctx);
    }

    @Override
    public Top visitStructure_declaration(IEC61131Parser.Structure_declarationContext ctx) {
        return super.visitStructure_declaration(ctx);
    }

    @Override
    public Top visitStructure_element_declaration(IEC61131Parser.Structure_element_declarationContext ctx) {
        return super.visitStructure_element_declaration(ctx);
    }

    @Override
    public Top visitStructure_initialization(IEC61131Parser.Structure_initializationContext ctx) {
        return super.visitStructure_initialization(ctx);
    }

    @Override
    public Top visitStructure_element_initialization(IEC61131Parser.Structure_element_initializationContext ctx) {
        return super.visitStructure_element_initialization(ctx);
    }

    @Override
    public Top visitString_type_declaration(IEC61131Parser.String_type_declarationContext ctx) {
        return super.visitString_type_declaration(ctx);
    }

    @Override
    public Top visitInput_declarations(IEC61131Parser.Input_declarationsContext ctx) {
        return super.visitInput_declarations(ctx);
    }

    @Override
    public Top visitInput_declaration(IEC61131Parser.Input_declarationContext ctx) {
        return super.visitInput_declaration(ctx);
    }

    @Override
    public Top visitEdge_declaration(IEC61131Parser.Edge_declarationContext ctx) {
        return super.visitEdge_declaration(ctx);
    }

    @Override
    public Top visitVar_init_decl(IEC61131Parser.Var_init_declContext ctx) {
        return super.visitVar_init_decl(ctx);
    }

    @Override
    public Top visitVar1_init_decl(IEC61131Parser.Var1_init_declContext ctx) {
        return super.visitVar1_init_decl(ctx);
    }

    @Override
    public Top visitArray_var_init_decl(IEC61131Parser.Array_var_init_declContext ctx) {
        return super.visitArray_var_init_decl(ctx);
    }

    @Override
    public Top visitStructured_var_init_decl(IEC61131Parser.Structured_var_init_declContext ctx) {
        return super.visitStructured_var_init_decl(ctx);
    }

    @Override
    public Top visitFb_name_decl(IEC61131Parser.Fb_name_declContext ctx) {
        return super.visitFb_name_decl(ctx);
    }

    @Override
    public Top visitOutput_declarations(IEC61131Parser.Output_declarationsContext ctx) {
        return super.visitOutput_declarations(ctx);
    }

    @Override
    public Top visitInput_output_declarations(IEC61131Parser.Input_output_declarationsContext ctx) {
        return super.visitInput_output_declarations(ctx);
    }

    @Override
    public Top visitVar_declaration(IEC61131Parser.Var_declarationContext ctx) {
        return super.visitVar_declaration(ctx);
    }

    @Override
    public Top visitTemp_var_decl(IEC61131Parser.Temp_var_declContext ctx) {
        return super.visitTemp_var_decl(ctx);
    }

    @Override
    public Top visitVar1_declaration(IEC61131Parser.Var1_declarationContext ctx) {
        return super.visitVar1_declaration(ctx);
    }

    @Override
    public Top visitPointer_var_declaration(IEC61131Parser.Pointer_var_declarationContext ctx) {
        return super.visitPointer_var_declaration(ctx);
    }

    @Override
    public Top visitArray_var_declaration(IEC61131Parser.Array_var_declarationContext ctx) {
        return super.visitArray_var_declaration(ctx);
    }

    @Override
    public Top visitStructured_var_declaration(IEC61131Parser.Structured_var_declarationContext ctx) {
        return super.visitStructured_var_declaration(ctx);
    }

    @Override
    public Top visitVar_declarations(IEC61131Parser.Var_declarationsContext ctx) {
        return super.visitVar_declarations(ctx);
    }

    @Override
    public Top visitRetentive_var_declarations(IEC61131Parser.Retentive_var_declarationsContext ctx) {
        return super.visitRetentive_var_declarations(ctx);
    }

    @Override
    public Top visitLocated_var_declarations(IEC61131Parser.Located_var_declarationsContext ctx) {
        return super.visitLocated_var_declarations(ctx);
    }

    @Override
    public Top visitLocated_var_decl(IEC61131Parser.Located_var_declContext ctx) {
        return super.visitLocated_var_decl(ctx);
    }

    @Override
    public Top visitExternal_var_declarations(IEC61131Parser.External_var_declarationsContext ctx) {
        return super.visitExternal_var_declarations(ctx);
    }

    @Override
    public Top visitExternal_declaration(IEC61131Parser.External_declarationContext ctx) {
        return super.visitExternal_declaration(ctx);
    }

    @Override
    public Top visitGlobal_var_declarations(IEC61131Parser.Global_var_declarationsContext ctx) {
        return super.visitGlobal_var_declarations(ctx);
    }

    @Override
    public Top visitGlobal_var_decl(IEC61131Parser.Global_var_declContext ctx) {
        return super.visitGlobal_var_decl(ctx);
    }

    @Override
    public Top visitGlobal_var_spec(IEC61131Parser.Global_var_specContext ctx) {
        return super.visitGlobal_var_spec(ctx);
    }

    @Override
    public Top visitLocated_var_spec_init(IEC61131Parser.Located_var_spec_initContext ctx) {
        return super.visitLocated_var_spec_init(ctx);
    }

    @Override
    public Top visitLocation(IEC61131Parser.LocationContext ctx) {
        return super.visitLocation(ctx);
    }

    @Override
    public Top visitIdentifier_list(IEC61131Parser.Identifier_listContext ctx) {
        return super.visitIdentifier_list(ctx);
    }

    @Override
    public Top visitString_var_declaration(IEC61131Parser.String_var_declarationContext ctx) {
        return super.visitString_var_declaration(ctx);
    }

    @Override
    public Top visitIncompl_located_var_declarations(IEC61131Parser.Incompl_located_var_declarationsContext ctx) {
        return super.visitIncompl_located_var_declarations(ctx);
    }

    @Override
    public Top visitIncompl_located_var_decl(IEC61131Parser.Incompl_located_var_declContext ctx) {
        return super.visitIncompl_located_var_decl(ctx);
    }

    @Override
    public Top visitVar_spec(IEC61131Parser.Var_specContext ctx) {
        return super.visitVar_spec(ctx);
    }

    @Override
    public Top visitFunction_declaration(IEC61131Parser.Function_declarationContext ctx) {
        return super.visitFunction_declaration(ctx);
    }

    @Override
    public Top visitIo_var_declarations(IEC61131Parser.Io_var_declarationsContext ctx) {
        return super.visitIo_var_declarations(ctx);
    }

    @Override
    public Top visitFunction_var_decls(IEC61131Parser.Function_var_declsContext ctx) {
        return super.visitFunction_var_decls(ctx);
    }

    @Override
    public Top visitVar2_init_decl(IEC61131Parser.Var2_init_declContext ctx) {
        return super.visitVar2_init_decl(ctx);
    }

    @Override
    public Top visitFunction_block_declaration(IEC61131Parser.Function_block_declarationContext ctx) {
        return super.visitFunction_block_declaration(ctx);
    }

    @Override
    public Top visitOther_var_declarations(IEC61131Parser.Other_var_declarationsContext ctx) {
        return super.visitOther_var_declarations(ctx);
    }

    @Override
    public Top visitTemp_var_decls(IEC61131Parser.Temp_var_declsContext ctx) {
        return super.visitTemp_var_decls(ctx);
    }

    @Override
    public Top visitNon_retentive_var_declarations(IEC61131Parser.Non_retentive_var_declarationsContext ctx) {
        return super.visitNon_retentive_var_declarations(ctx);
    }

    @Override
    public Top visitProgram_declaration(IEC61131Parser.Program_declarationContext ctx) {
        return super.visitProgram_declaration(ctx);
    }

    @Override
    public Top visitProgram_access_decls(IEC61131Parser.Program_access_declsContext ctx) {
        return super.visitProgram_access_decls(ctx);
    }

    @Override
    public Top visitProgram_access_decl(IEC61131Parser.Program_access_declContext ctx) {
        return super.visitProgram_access_decl(ctx);
    }

    @Override
    public Top visitConfiguration_declaration(IEC61131Parser.Configuration_declarationContext ctx) {
        return super.visitConfiguration_declaration(ctx);
    }

    @Override
    public Top visitResource_declaration(IEC61131Parser.Resource_declarationContext ctx) {
        return super.visitResource_declaration(ctx);
    }

    @Override
    public Top visitSingle_resource_declaration(IEC61131Parser.Single_resource_declarationContext ctx) {
        return super.visitSingle_resource_declaration(ctx);
    }

    @Override
    public Top visitAccess_declarations(IEC61131Parser.Access_declarationsContext ctx) {
        return super.visitAccess_declarations(ctx);
    }

    @Override
    public Top visitAccess_declaration(IEC61131Parser.Access_declarationContext ctx) {
        return super.visitAccess_declaration(ctx);
    }

    @Override
    public Top visitAccess_path(IEC61131Parser.Access_pathContext ctx) {
        return super.visitAccess_path(ctx);
    }

    @Override
    public Top visitGlobal_var_reference(IEC61131Parser.Global_var_referenceContext ctx) {
        return super.visitGlobal_var_reference(ctx);
    }

    @Override
    public Top visitProgram_output_reference(IEC61131Parser.Program_output_referenceContext ctx) {
        return super.visitProgram_output_reference(ctx);
    }

    @Override
    public Top visitDirection(IEC61131Parser.DirectionContext ctx) {
        return super.visitDirection(ctx);
    }

    @Override
    public Top visitTask_configuration(IEC61131Parser.Task_configurationContext ctx) {
        return super.visitTask_configuration(ctx);
    }

    @Override
    public Top visitTask_initialization(IEC61131Parser.Task_initializationContext ctx) {
        return super.visitTask_initialization(ctx);
    }

    @Override
    public Top visitData_source(IEC61131Parser.Data_sourceContext ctx) {
        return super.visitData_source(ctx);
    }

    @Override
    public Top visitProgram_configuration(IEC61131Parser.Program_configurationContext ctx) {
        return super.visitProgram_configuration(ctx);
    }

    @Override
    public Top visitProg_conf_elements(IEC61131Parser.Prog_conf_elementsContext ctx) {
        return super.visitProg_conf_elements(ctx);
    }

    @Override
    public Top visitProg_conf_element(IEC61131Parser.Prog_conf_elementContext ctx) {
        return super.visitProg_conf_element(ctx);
    }

    @Override
    public Top visitFb_task(IEC61131Parser.Fb_taskContext ctx) {
        return super.visitFb_task(ctx);
    }

    @Override
    public Top visitProg_cnxn(IEC61131Parser.Prog_cnxnContext ctx) {
        return super.visitProg_cnxn(ctx);
    }

    @Override
    public Top visitProg_data_source(IEC61131Parser.Prog_data_sourceContext ctx) {
        return super.visitProg_data_source(ctx);
    }

    @Override
    public Top visitData_sink(IEC61131Parser.Data_sinkContext ctx) {
        return super.visitData_sink(ctx);
    }

    @Override
    public Top visitInstance_specific_initializations(IEC61131Parser.Instance_specific_initializationsContext ctx) {
        return super.visitInstance_specific_initializations(ctx);
    }

    @Override
    public Top visitInstance_specific_init(IEC61131Parser.Instance_specific_initContext ctx) {
        return super.visitInstance_specific_init(ctx);
    }

    @Override
    public Top visitExpression(IEC61131Parser.ExpressionContext ctx) {
        return super.visitExpression(ctx);
    }

    @Override
    public Top visitPrimary_expression(IEC61131Parser.Primary_expressionContext ctx) {
        return super.visitPrimary_expression(ctx);
    }

    @Override
    public Top visitFunctioncall(IEC61131Parser.FunctioncallContext ctx) {
        return super.visitFunctioncall(ctx);
    }

    @Override
    public Top visitParam_assignment(IEC61131Parser.Param_assignmentContext ctx) {
        return super.visitParam_assignment(ctx);
    }

    @Override
    public Top visitStatement_list(IEC61131Parser.Statement_listContext ctx) {
        return super.visitStatement_list(ctx);
    }

    @Override
    public Top visitStatement(IEC61131Parser.StatementContext ctx) {
        return super.visitStatement(ctx);
    }

    @Override
    public Top visitAssignment_statement(IEC61131Parser.Assignment_statementContext ctx) {
        return super.visitAssignment_statement(ctx);
    }

    @Override
    public Top visitVariable(IEC61131Parser.VariableContext ctx) {
        return super.visitVariable(ctx);
    }

    @Override
    public Top visitSymbolic_variable(IEC61131Parser.Symbolic_variableContext ctx) {
        return super.visitSymbolic_variable(ctx);
    }

    @Override
    public Top visitSubscript_list(IEC61131Parser.Subscript_listContext ctx) {
        return super.visitSubscript_list(ctx);
    }

    @Override
    public Top visitDirect_variable(IEC61131Parser.Direct_variableContext ctx) {
        return super.visitDirect_variable(ctx);
    }

    @Override
    public Top visitSubprogram_control_statement(IEC61131Parser.Subprogram_control_statementContext ctx) {
        return super.visitSubprogram_control_statement(ctx);
    }

    @Override
    public Top visitSelection_statement(IEC61131Parser.Selection_statementContext ctx) {
        return super.visitSelection_statement(ctx);
    }

    @Override
    public Top visitIf_statement(IEC61131Parser.If_statementContext ctx) {
        return super.visitIf_statement(ctx);
    }

    @Override
    public Top visitCase_statement(IEC61131Parser.Case_statementContext ctx) {
        return super.visitCase_statement(ctx);
    }

    @Override
    public Top visitCase_element(IEC61131Parser.Case_elementContext ctx) {
        return super.visitCase_element(ctx);
    }

    @Override
    public Top visitCase_list(IEC61131Parser.Case_listContext ctx) {
        return super.visitCase_list(ctx);
    }

    @Override
    public Top visitCase_list_element(IEC61131Parser.Case_list_elementContext ctx) {
        return super.visitCase_list_element(ctx);
    }

    @Override
    public Top visitIteration_statement(IEC61131Parser.Iteration_statementContext ctx) {
        return super.visitIteration_statement(ctx);
    }

    @Override
    public Top visitFor_statement(IEC61131Parser.For_statementContext ctx) {
        return super.visitFor_statement(ctx);
    }

    @Override
    public Top visitFor_list(IEC61131Parser.For_listContext ctx) {
        return super.visitFor_list(ctx);
    }

    @Override
    public Top visitWhile_statement(IEC61131Parser.While_statementContext ctx) {
        return super.visitWhile_statement(ctx);
    }

    @Override
    public Top visitRepeat_statement(IEC61131Parser.Repeat_statementContext ctx) {
        return super.visitRepeat_statement(ctx);
    }

    @Override
    public Top visitExit_statement(IEC61131Parser.Exit_statementContext ctx) {
        return super.visitExit_statement(ctx);
    }

    @Override
    public Top visitStart_sfc(IEC61131Parser.Start_sfcContext ctx) {
        return super.visitStart_sfc(ctx);
    }

    @Override
    public Top visitGoto_declaration(IEC61131Parser.Goto_declarationContext ctx) {
        return super.visitGoto_declaration(ctx);
    }

    @Override
    public Top visitAction_declaration(IEC61131Parser.Action_declarationContext ctx) {
        return super.visitAction_declaration(ctx);
    }

    @Override
    public Top visitStep_declaration(IEC61131Parser.Step_declarationContext ctx) {
        return super.visitStep_declaration(ctx);
    }

    @Override
    public Top visitEvent(IEC61131Parser.EventContext ctx) {
        return super.visitEvent(ctx);
    }
}
