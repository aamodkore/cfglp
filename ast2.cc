#include <iostream>
#include <fstream>

using namespace std;

#include "user-options.hh"
#include "error-display.hh"
#include "local-environment.hh"

#include "symbol-table.hh"
#include "ast.hh"

Relational_Expr_Ast::Relational_Expr_Ast() {}
Relational_Expr_Ast::~Relational_Expr_Ast() {}

Data_Type Relational_Expr_Ast::get_data_type() {
	return int_data_type ;
}


void Relational_Expr_Ast::print_ast(ostream & file_buffer) {

}

void Relational_Expr_Ast::print_value(Local_Environment & eval_env, ostream & file_buffer) {

}


Eval_Result & Relational_Expr_Ast::get_value_of_evaluation(Local_Environment & eval_env) {

}

void Relational_Expr_Ast::set_value_of_evaluation(Local_Environment & eval_env, Eval_Result & result) {

}

Eval_Result & Relational_Expr_Ast::evaluate(Local_Environment & eval_env, ostream & file_buffer) {}
