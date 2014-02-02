#include <iostream>
#include <fstream>

using namespace std;

#include "user-options.hh"
#include "error-display.hh"
#include "local-environment.hh"

#include "symbol-table.hh"
#include "ast.hh"

Relational_Expr_Ast::Relational_Expr_Ast(Ast* temp_lhs, Relational_Operator opr, Ast* temp_rhs) {
	relational_op = opr ;
	lhs = temp_lhs ;
	rhs = temp_rhs ;
}

Relational_Expr_Ast::~Relational_Expr_Ast() {
	if (!lhs) delete lhs ;
	if (!rhs) delete rhs ;
}

Data_Type Relational_Expr_Ast::get_data_type() { return int_data_type ; }


void Relational_Expr_Ast::print_ast(ostream & file_buffer) {

	file_buffer << endl << AST_NODE_SPACE << "Condition: ";

	switch(relational_op) {
		case greater_than_op   : file_buffer << "GT" ; break ;
		case greater_equals_op : file_buffer << "GE" ; break ;
		case less_than_op      : file_buffer << "LT" ; break ;
		case less_equals_op    : file_buffer << "LE" ; break ;
		case equals_op         : file_buffer << "EQ" ; break ;
		case not_equals_op     : file_buffer << "NE" ; break ;
		default : file_buffer << "nop" ; break ;
	}
	file_buffer << endl ;

	file_buffer << AST_SUB_NODE_SPACE << "LHS (";
	lhs->print_ast(file_buffer);
	file_buffer << ")\n";

	file_buffer << AST_SUB_NODE_SPACE << "RHS (";
	rhs->print_ast(file_buffer);
	file_buffer << ")";
}


Eval_Result & Relational_Expr_Ast::evaluate(Local_Environment & eval_env, ostream & file_buffer) {
	Eval_Result & lhsresult = lhs->evaluate(eval_env, file_buffer);
	Eval_Result & rhsresult = rhs->evaluate(eval_env, file_buffer);

	if (!lhsresult.is_variable_defined())
		report_error("Variable should be defined on LHS of comparison.", NOLINE);
	if (!rhsresult.is_variable_defined())
		report_error("Variable should be defined on RHS of comparison.", NOLINE);


	Eval_Result_Value_Int * result = new Eval_Result_Value_Int() ;
	
	bool value ;
	switch(relational_op) {
		case greater_than_op   : value = (lhsresult.get_value() >  rhsresult.get_value()); break ;
		case greater_equals_op : value = (lhsresult.get_value() >= rhsresult.get_value()); break ;
		case less_than_op      : value = (lhsresult.get_value() <  rhsresult.get_value()); break ;
		case less_equals_op    : value = (lhsresult.get_value() <= rhsresult.get_value()); break ;
		case equals_op         : value = (lhsresult.get_value() == rhsresult.get_value()); break ;
		case not_equals_op     : value = (lhsresult.get_value() != rhsresult.get_value()); break ;
		default : value = false ;
	}

	result->set_value(value?1:0) ;
	return *result;
}
