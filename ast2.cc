/*********************************************************************************************

                                cfglp : A CFG Language Processor
                                --------------------------------

           About:

           Implemented   by  Tanu  Kanvar (tanu@cse.iitb.ac.in) and Uday
           Khedker    (http://www.cse.iitb.ac.in/~uday)  for the courses
           cs302+cs306: Language  Processors  (theory and  lab)  at  IIT
           Bombay.

           Release  date  Jan  15, 2013.  Copyrights  reserved  by  Uday
           Khedker. This  implemenation  has been made  available purely
           for academic purposes without any warranty of any kind.

           Documentation (functionality, manual, and design) and related
           tools are  available at http://www.cse.iitb.ac.in/~uday/cfglp
           
***********************************************************************************************/

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


	Eval_Result_Value_Bool * result = new Eval_Result_Value_Bool() ;
	
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

	// delete & lhsresult ;
	// delete & rhsresult ;
	return *result;
}
/********************************************************************************/
Arithmetic_Expr_Ast::Arithmetic_Expr_Ast() {}

Arithmetic_Expr_Ast::~Arithmetic_Expr_Ast() {}

bool Arithmetic_Expr_Ast::check_ast(int line) {
	if (lhs->get_data_type() == rhs->get_data_type())
	{
		node_data_type = lhs->get_data_type();
		return true;
	}

	report_error("Arithmetic statement data type not compatible", line);
}

Data_Type Arithmetic_Expr_Ast::get_data_type() {
  return node_data_type;
}

/******************************************************************************/

Plus_Ast::Plus_Ast(Ast * l, Ast * r) {
  lhs = l;
  rhs = r;
}

Plus_Ast::~Plus_Ast() {}

Data_Type Plus_Ast::get_data_type() {
  return node_data_type;
}

void Plus_Ast::print_ast(ostream & file_buffer) {
  
}

Eval_Result & Plus_Ast::evaluate(Local_Environment & eval_env, ostream & file_buffer) {
}
  
/**********************************************************************************/

Minus_Ast::Minus_Ast(Ast * l, Ast * r) {
  lhs = l;
  rhs = r;
}

Minus_Ast::~Minus_Ast() {}

Data_Type Minus_Ast::get_data_type() {
  return node_data_type;
}

void Minus_Ast::print_ast(ostream & file_buffer) {
  
}

Eval_Result & Minus_Ast::evaluate(Local_Environment & eval_env, ostream & file_buffer) {
}
/**********************************************************************************/

Multiplication_Ast::Multiplication_Ast(Ast * l, Ast * r) {
  lhs = l;
  rhs = r;
}

Multiplication_Ast::~Multiplication_Ast() {}

Data_Type Multiplication_Ast::get_data_type() {
  return node_data_type;
}

void Multiplication_Ast::print_ast(ostream & file_buffer) {
  
}

Eval_Result & Multiplication_Ast::evaluate(Local_Environment & eval_env, ostream & file_buffer) {
}
/**********************************************************************************/

Division_Ast::Division_Ast(Ast * l, Ast * r) {
  lhs = l;
  rhs = r;
}

Division_Ast::~Division_Ast() {}

Data_Type Division_Ast::get_data_type() {
  return node_data_type;
}

void Division_Ast::print_ast(ostream & file_buffer) {
  
}

Eval_Result & Division_Ast::evaluate(Local_Environment & eval_env, ostream & file_buffer) {
}
/**********************************************************************************/

Unary_Ast::Unary_Ast(Ast * r) {
  lhs = NULL;
  rhs = r;
}

Unary_Ast::~Unary_Ast() {}

bool Unary_Ast::check_ast(int line) {
  if(rhs->get_data_type() == int_data_type || rhs->get_data_type() == float_data_type ){
    node_data_type = rhs->get_data_type();
    return true;
  }
  report_error("Unary expression data type not compatible", line);
}

Data_Type Unary_Ast::get_data_type() {
  return node_data_type;
}

void Unary_Ast::print_ast(ostream & file_buffer) {
  
}

Eval_Result & Unary_Ast::evaluate(Local_Environment & eval_env, ostream & file_buffer) {
}
/***********************************************************************************/


