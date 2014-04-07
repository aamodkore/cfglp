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
#include <iomanip>
#include <fstream>

using namespace std;

#include"common-classes.hh"
#include"error-display.hh"
#include"user-options.hh"
#include"local-environment.hh"
#include"icode.hh"
#include"reg-alloc.hh"
#include"symbol-table.hh"
#include"ast.hh"
#include"basic-block.hh"
#include"procedure.hh"
#include"program.hh"

Relational_Expr_Ast::Relational_Expr_Ast(Ast* temp_lhs, Relational_Operator opr, Ast* temp_rhs) {
  relational_op = opr ;
  lhs = temp_lhs ;
  rhs = temp_rhs ;
}

Relational_Expr_Ast::~Relational_Expr_Ast() {
  if (!lhs) delete lhs ;
  if (!rhs) delete rhs ;
}

Data_Type Relational_Expr_Ast::get_data_type() { return node_data_type; }

bool Relational_Expr_Ast::check_ast() {
  if (lhs->get_data_type() == rhs->get_data_type())
    {
      node_data_type = int_data_type;
      return true;
    }

  cout << "Relational statement data type not compatible";
}



void Relational_Expr_Ast::print(ostream & file_buffer) {

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
  file_buffer <<  endl ;

  file_buffer << AST_SUB_NODE_SPACE << "LHS (";
  lhs->print(file_buffer);
  file_buffer << ")" << "\n";

  file_buffer << AST_SUB_NODE_SPACE << "RHS (";
  rhs->print(file_buffer);
  file_buffer << ")";
}


Eval_Result & Relational_Expr_Ast::evaluate(Local_Environment & eval_env, ostream & file_buffer) {
  Eval_Result & lhsresult = lhs->evaluate(eval_env, file_buffer);
  Eval_Result & rhsresult = rhs->evaluate(eval_env, file_buffer);

  if (!lhsresult.is_variable_defined())
    cout << "Variable should be defined on LHS of comparison.";
  if (!rhsresult.is_variable_defined())
    cout << "Variable should be defined on RHS of comparison.";

  Eval_Result* result;
  if(node_data_type == float_data_type) {
    result = new Eval_Result_Value_Float();
  }
  else {
    result = new Eval_Result_Value_Bool();
  }
	
  bool value ;
  if(lhsresult.get_result_enum() == int_result || lhsresult.get_result_enum() == bool_result) {
    switch(relational_op) {
    case greater_than_op   : value = (lhsresult.get_int_value() >  rhsresult.get_int_value()); break ;
    case greater_equals_op : value = (lhsresult.get_int_value() >= rhsresult.get_int_value()); break ;
    case less_than_op      : value = (lhsresult.get_int_value() <  rhsresult.get_int_value()); break ;
    case less_equals_op    : value = (lhsresult.get_int_value() <= rhsresult.get_int_value()); break ;
    case equals_op         : value = (lhsresult.get_int_value() == rhsresult.get_int_value()); break ;
    case not_equals_op     : value = (lhsresult.get_int_value() != rhsresult.get_int_value()); break ;
    default : value = false ;
    }
  }
  else if(lhsresult.get_result_enum() == float_result) {
    switch(relational_op) {
    case greater_than_op   : value = (lhsresult.get_value_float() >  rhsresult.get_value_float()); break ;
    case greater_equals_op : value = (lhsresult.get_value_float() >= rhsresult.get_value_float()); break ;
    case less_than_op      : value = (lhsresult.get_value_float() <  rhsresult.get_value_float()); break ;
    case less_equals_op    : value = (lhsresult.get_value_float() <= rhsresult.get_value_float()); break ; 
    case equals_op         : value = (lhsresult.get_value_float() == rhsresult.get_value_float()); break ;
    case not_equals_op     : value = (lhsresult.get_value_float() != rhsresult.get_value_float()); break ;
    default : value = false ;
    }
  }
  if(node_data_type == float_data_type) {
    result->set_value_float(value?1.0:0.0) ;
  }
  else {
    result->set_value(value?1:0) ;
  }

  // delete & lhsresult ;
  // delete & rhsresult ;
  return *result;
}
Code_For_Ast & Relational_Expr_Ast::compile(){		
	CHECK_INVARIANT((lhs != NULL), "LHS cannot be null");
	CHECK_INVARIANT((rhs != NULL), "RHS cannot be null");
	
  Code_For_Ast & lhs_stmt = lhs->compile();
	Register_Descriptor * lreg = lhs_stmt.get_reg();
	Code_For_Ast & rhs_stmt = rhs->compile();
	Register_Descriptor * rreg = rhs_stmt.get_reg();

	list<Icode_Stmt *> & ic_list = *new list<Icode_Stmt *>;

	Ics_Opd * lhs_reg = new Register_Addr_Opd(lreg);
	Ics_Opd * rhs_reg = new Register_Addr_Opd(rreg);
	
	if (lhs_stmt.get_icode_list().empty() == false)
		ic_list = lhs_stmt.get_icode_list();
	if (rhs_stmt.get_icode_list().empty() == false)
		ic_list.splice(ic_list.end(), rhs_stmt.get_icode_list());
	
	Register_Descriptor * result_reg = machine_dscr_object.get_new_register();
	result_reg->set_used_for_expr_result();
	Ics_Opd * register_result = new Register_Addr_Opd(result_reg);

	switch(relational_op) {
	case greater_than_op   : 
		ic_list.push_back(new Compute_IC_Stmt(sgt, register_result, lhs_reg, rhs_reg)) ;
		break ;
	case greater_equals_op : 
		ic_list.push_back(new Compute_IC_Stmt(sge, register_result, lhs_reg, rhs_reg)) ;
		break ;
	case less_than_op      : 
		ic_list.push_back(new Compute_IC_Stmt(slt, register_result, lhs_reg, rhs_reg)) ;
		break ;
	case less_equals_op    : 
		ic_list.push_back(new Compute_IC_Stmt(sle, register_result, lhs_reg, rhs_reg)) ;
		break ;
	case equals_op         : 
		ic_list.push_back(new Compute_IC_Stmt(seq, register_result, lhs_reg, rhs_reg)) ;
		break ;
	case not_equals_op     : 
		ic_list.push_back(new Compute_IC_Stmt(sne, register_result, lhs_reg, rhs_reg)) ;
		break ;
	}
	
	// Free the previous result register.
	lreg->reset_use_for_expr_result();
	lreg->clear_lra_symbol_list();
	rreg->reset_use_for_expr_result();
	rreg->clear_lra_symbol_list();
	Code_For_Ast & rel_expr_code = *new Code_For_Ast(ic_list, result_reg);
	return rel_expr_code;
}
Code_For_Ast & Relational_Expr_Ast::compile_and_optimize_ast(Lra_Outcome & lra) {
	CHECK_INVARIANT((lhs != NULL), "LHS cannot be null");
	CHECK_INVARIANT((rhs != NULL), "RHS cannot be null");
	
	Register_Descriptor * result_reg = NULL;
	/*
	if(lra.is_destination_register()) {
	 // cout << "Inherited from above\n";
	  result_reg = lra.get_register();
	}
	else {
	   result_reg = NULL;
	}
	*/ 

	lra.optimize_lra(mc_2r, NULL, lhs);
	Code_For_Ast & lhs_stmt = lhs->compile_and_optimize_ast(lra);
	Register_Descriptor * lreg = lhs_stmt.get_reg();

	lra.optimize_lra(mc_2r, NULL, rhs);
	Code_For_Ast & rhs_stmt = rhs->compile_and_optimize_ast(lra);
	Register_Descriptor * rreg = rhs_stmt.get_reg();

	list<Icode_Stmt *> & ic_list = *new list<Icode_Stmt *>;

	Ics_Opd * lhs_reg = new Register_Addr_Opd(lreg);
	Ics_Opd * rhs_reg = new Register_Addr_Opd(rreg);
	
	if (lhs_stmt.get_icode_list().empty() == false)
		ic_list = lhs_stmt.get_icode_list();
	if (rhs_stmt.get_icode_list().empty() == false)
		ic_list.splice(ic_list.end(), rhs_stmt.get_icode_list());
	
	//	cout << "In Relational\n";
	if(result_reg == NULL) {
	  result_reg = machine_dscr_object.get_new_register();
	}
	result_reg->set_used_for_expr_result();
	Ics_Opd * register_result = new Register_Addr_Opd(result_reg);

	switch(relational_op) {
	case greater_than_op   : 
		ic_list.push_back(new Compute_IC_Stmt(sgt, register_result, lhs_reg, rhs_reg)) ;
		break ;
	case greater_equals_op : 
		ic_list.push_back(new Compute_IC_Stmt(sge, register_result, lhs_reg, rhs_reg)) ;
		break ;
	case less_than_op      : 
		ic_list.push_back(new Compute_IC_Stmt(slt, register_result, lhs_reg, rhs_reg)) ;
		break ;
	case less_equals_op    : 
		ic_list.push_back(new Compute_IC_Stmt(sle, register_result, lhs_reg, rhs_reg)) ;
		break ;
	case equals_op         : 
		ic_list.push_back(new Compute_IC_Stmt(seq, register_result, lhs_reg, rhs_reg)) ;
		break ;
	case not_equals_op     : 
		ic_list.push_back(new Compute_IC_Stmt(sne, register_result, lhs_reg, rhs_reg)) ;
		break ;
	}
	
	// Free the previous result register.
	lreg->reset_use_for_expr_result();
	rreg->reset_use_for_expr_result();
	Code_For_Ast & rel_expr_code = *new Code_For_Ast(ic_list, result_reg);
	return rel_expr_code;
}

/********************************************************************************/
Arithmetic_Expr_Ast::Arithmetic_Expr_Ast() {}

Arithmetic_Expr_Ast::~Arithmetic_Expr_Ast() {}

bool Arithmetic_Expr_Ast::check_ast() {
  if (lhs->get_data_type() == rhs->get_data_type())
    {
      node_data_type = lhs->get_data_type();
      return true;
    }
  cout << "Arithmetic statement data type not compatible";
}

Data_Type Arithmetic_Expr_Ast::get_data_type() {
  return node_data_type;
}

Code_For_Ast & Arithmetic_Expr_Ast::compile(){}
Code_For_Ast & Arithmetic_Expr_Ast::compile_and_optimize_ast(Lra_Outcome & lra){}

/******************************************************************************/

Plus_Ast::Plus_Ast(Ast * l, Ast * r) {
  lhs = l;
  rhs = r;
}

Plus_Ast::~Plus_Ast() {}

Data_Type Plus_Ast::get_data_type() {
  return node_data_type;
}

void Plus_Ast::print(ostream & file_buffer) {
  file_buffer << endl << AST_NODE_SPACE << "Arith: PLUS" << endl;

  file_buffer << AST_SUB_NODE_SPACE << "LHS (";
  lhs->print(file_buffer);
  file_buffer << ")" <<  "\n";
  
  file_buffer << AST_SUB_NODE_SPACE << "RHS (";
  rhs->print(file_buffer);
  file_buffer << ")";
}

Eval_Result & Plus_Ast::evaluate(Local_Environment & eval_env, ostream & file_buffer) {
  Eval_Result & lhs_result = lhs->evaluate(eval_env, file_buffer);
  Eval_Result & rhs_result = rhs->evaluate(eval_env, file_buffer);
 
  if(node_data_type == int_data_type) {
    Eval_Result * result = new Eval_Result_Value_Int(); 
    if(lhs_result.get_result_enum() == int_result || lhs_result.get_result_enum() == bool_result) {
      result->set_value( lhs_result.get_int_value() + rhs_result.get_int_value());
    }
    else if(lhs_result.get_result_enum() == float_result) {
      result->set_value( (int) (lhs_result.get_value_float() + rhs_result.get_value_float()));
    }
    return * result;
  }
  
  else if(node_data_type == float_data_type) {
    Eval_Result * result = new Eval_Result_Value_Float(); 
    if(lhs_result.get_result_enum() == int_result || lhs_result.get_result_enum() == bool_result) {
      result->set_value_float( (float) (lhs_result.get_int_value() + rhs_result.get_int_value()));
    }
    else if(lhs_result.get_result_enum() == float_result) {
      result->set_value_float( lhs_result.get_value_float() + rhs_result.get_value_float());
    }
    return * result;
  }

  else {
    cout << "Data-Type not defined for addition\n";
  }
}

Code_For_Ast & Plus_Ast::compile() {
  CHECK_INVARIANT((lhs != NULL), "LHS cannot be null");
  CHECK_INVARIANT((rhs != NULL), "RHS cannot be null");
  
  Code_For_Ast & lhs_stmt = lhs->compile();
  Register_Descriptor * lreg = lhs_stmt.get_reg();
  Code_For_Ast & rhs_stmt = rhs->compile();
  Register_Descriptor * rreg = rhs_stmt.get_reg();

  CHECK_INVARIANT((lreg->get_value_type()==rreg->get_value_type()), 
                  "LHS and RHS are incompatible data types")

  list<Icode_Stmt *> & ic_list = *new list<Icode_Stmt *>;

  Ics_Opd * lhs_reg = new Register_Addr_Opd(lreg);
  Ics_Opd * rhs_reg = new Register_Addr_Opd(rreg);
  
  if (lhs_stmt.get_icode_list().empty() == false)
    ic_list = lhs_stmt.get_icode_list();
  if (rhs_stmt.get_icode_list().empty() == false)
    ic_list.splice(ic_list.end(), rhs_stmt.get_icode_list());
  
  Register_Descriptor * result_reg ;
  Tgt_Op opr ;
  if (lreg->get_value_type() == int_num) {
    result_reg = machine_dscr_object.get_new_register();
    opr = add ;
  }
  if (lreg->get_value_type() == float_num) {
    result_reg = machine_dscr_object.get_new_float_register();
    opr = add_d ;
  }
  result_reg->set_used_for_expr_result();
  Ics_Opd * register_result = new Register_Addr_Opd(result_reg);

  ic_list.push_back(new Compute_IC_Stmt(opr, register_result, lhs_reg, rhs_reg)) ;
  
  // Free the previous result register.
  lreg->reset_use_for_expr_result();
  lreg->clear_lra_symbol_list();
  rreg->reset_use_for_expr_result();
  rreg->clear_lra_symbol_list();
  Code_For_Ast & rel_expr_code = *new Code_For_Ast(ic_list, result_reg);
  return rel_expr_code;
}


Code_For_Ast & Plus_Ast::compile_and_optimize_ast(Lra_Outcome & lra) {
  CHECK_INVARIANT((lhs != NULL), "LHS cannot be null");
  CHECK_INVARIANT((rhs != NULL), "RHS cannot be null");
  
  Register_Descriptor * result_reg = NULL;
  
  lra.optimize_lra(mc_2r, NULL, lhs);
  Code_For_Ast & lhs_stmt = lhs->compile_and_optimize_ast(lra);
  Register_Descriptor * lreg = lhs_stmt.get_reg();

  lra.optimize_lra(mc_2r, NULL, rhs);
  Code_For_Ast & rhs_stmt = rhs->compile_and_optimize_ast(lra);
  Register_Descriptor * rreg = rhs_stmt.get_reg();

  list<Icode_Stmt *> & ic_list = *new list<Icode_Stmt *>;

  Ics_Opd * lhs_reg = new Register_Addr_Opd(lreg);
  Ics_Opd * rhs_reg = new Register_Addr_Opd(rreg);
  
  if (lhs_stmt.get_icode_list().empty() == false)
    ic_list = lhs_stmt.get_icode_list();
  if (rhs_stmt.get_icode_list().empty() == false)
    ic_list.splice(ic_list.end(), rhs_stmt.get_icode_list());
  
  Tgt_Op opr ;
  if (lreg->get_value_type() == int_num) {
    if (!result_reg) result_reg = machine_dscr_object.get_new_register();
    opr = add ;
  }
  if (lreg->get_value_type() == float_num) {
    if(!result_reg) result_reg = machine_dscr_object.get_new_float_register();
    opr = add_d ;
  }
  result_reg->set_used_for_expr_result();
  Ics_Opd * register_result = new Register_Addr_Opd(result_reg);

  ic_list.push_back(new Compute_IC_Stmt(opr, register_result, lhs_reg, rhs_reg)) ;
  
  // Free the previous result register.
  lreg->reset_use_for_expr_result();
  rreg->reset_use_for_expr_result();
  Code_For_Ast & rel_expr_code = *new Code_For_Ast(ic_list, result_reg);
  return rel_expr_code;
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

void Minus_Ast::print(ostream & file_buffer) {
  file_buffer << endl << AST_NODE_SPACE << "Arith: MINUS" << endl;

  file_buffer << AST_SUB_NODE_SPACE << "LHS (";
  lhs->print(file_buffer);
  file_buffer << ")\n";
  
  file_buffer << AST_SUB_NODE_SPACE << "RHS (";
  rhs->print(file_buffer);
  file_buffer << ")";
}

Eval_Result & Minus_Ast::evaluate(Local_Environment & eval_env, ostream & file_buffer) {
  Eval_Result & lhs_result = lhs->evaluate(eval_env, file_buffer);
  Eval_Result & rhs_result = rhs->evaluate(eval_env, file_buffer);
  
  if(node_data_type == int_data_type) {
    Eval_Result * result = new Eval_Result_Value_Int(); 
    if(lhs_result.get_result_enum() == int_result || lhs_result.get_result_enum() == bool_result) {
      result->set_value( lhs_result.get_int_value() - rhs_result.get_int_value());
    }
    else if(lhs_result.get_result_enum() == float_result) {
      result->set_value( (int) (lhs_result.get_value_float() - rhs_result.get_value_float()));
    }
    return * result;
  }
  
  else if(node_data_type == float_data_type) {
    Eval_Result * result = new Eval_Result_Value_Float(); 
    if(lhs_result.get_result_enum() == int_result || lhs_result.get_result_enum() == bool_result) {
      result->set_value_float( (float) (lhs_result.get_int_value() - rhs_result.get_int_value()));
    }
    else if(lhs_result.get_result_enum() == float_result) {
      result->set_value_float( lhs_result.get_value_float() - rhs_result.get_value_float());
    }
    return * result;
  }

  else {
    cout << "Data-Type not defined for addition\n";
  }
}

Code_For_Ast & Minus_Ast::compile() {
  CHECK_INVARIANT((lhs != NULL), "LHS cannot be null");
  CHECK_INVARIANT((rhs != NULL), "RHS cannot be null");
  
  Code_For_Ast & lhs_stmt = lhs->compile();
  Register_Descriptor * lreg = lhs_stmt.get_reg();
  Code_For_Ast & rhs_stmt = rhs->compile();
  Register_Descriptor * rreg = rhs_stmt.get_reg();

  CHECK_INVARIANT((lreg->get_value_type()==rreg->get_value_type()), 
                  "LHS and RHS are incompatible data types")

  list<Icode_Stmt *> & ic_list = *new list<Icode_Stmt *>;

  Ics_Opd * lhs_reg = new Register_Addr_Opd(lreg);
  Ics_Opd * rhs_reg = new Register_Addr_Opd(rreg);
  
  if (lhs_stmt.get_icode_list().empty() == false)
    ic_list = lhs_stmt.get_icode_list();
  if (rhs_stmt.get_icode_list().empty() == false)
    ic_list.splice(ic_list.end(), rhs_stmt.get_icode_list());
  
  Register_Descriptor * result_reg ;
  Tgt_Op opr ;
  if (lreg->get_value_type() == int_num) {
    result_reg = machine_dscr_object.get_new_register();
    opr = sub ;
  }
  if (lreg->get_value_type() == float_num) {
    result_reg = machine_dscr_object.get_new_float_register();
    opr = sub_d ;
  }
  result_reg->set_used_for_expr_result();
  Ics_Opd * register_result = new Register_Addr_Opd(result_reg);

  ic_list.push_back(new Compute_IC_Stmt(opr, register_result, lhs_reg, rhs_reg)) ;
  
  // Free the previous result register.
  lreg->reset_use_for_expr_result();
  lreg->clear_lra_symbol_list();
  rreg->reset_use_for_expr_result();
  rreg->clear_lra_symbol_list();
  Code_For_Ast & rel_expr_code = *new Code_For_Ast(ic_list, result_reg);
  return rel_expr_code;
}


Code_For_Ast & Minus_Ast::compile_and_optimize_ast(Lra_Outcome & lra) {
  CHECK_INVARIANT((lhs != NULL), "LHS cannot be null");
  CHECK_INVARIANT((rhs != NULL), "RHS cannot be null");
  
  Register_Descriptor * result_reg = NULL;
  
  
  lra.optimize_lra(mc_2r, NULL, lhs);
  Code_For_Ast & lhs_stmt = lhs->compile_and_optimize_ast(lra);
  Register_Descriptor * lreg = lhs_stmt.get_reg();

  lra.optimize_lra(mc_2r, NULL, rhs);
  Code_For_Ast & rhs_stmt = rhs->compile_and_optimize_ast(lra);
  Register_Descriptor * rreg = rhs_stmt.get_reg();

  list<Icode_Stmt *> & ic_list = *new list<Icode_Stmt *>;

  Ics_Opd * lhs_reg = new Register_Addr_Opd(lreg);
  Ics_Opd * rhs_reg = new Register_Addr_Opd(rreg);
  
  if (lhs_stmt.get_icode_list().empty() == false)
    ic_list = lhs_stmt.get_icode_list();
  if (rhs_stmt.get_icode_list().empty() == false)
    ic_list.splice(ic_list.end(), rhs_stmt.get_icode_list());
  
  Tgt_Op opr ;
  if (lreg->get_value_type() == int_num) {
    if (!result_reg) result_reg = machine_dscr_object.get_new_register();
    opr = sub ;
  }
  if (lreg->get_value_type() == float_num) {
    if(!result_reg) result_reg = machine_dscr_object.get_new_float_register();
    opr = sub_d ;
  }
  result_reg->set_used_for_expr_result();
  Ics_Opd * register_result = new Register_Addr_Opd(result_reg);

  ic_list.push_back(new Compute_IC_Stmt(opr, register_result, lhs_reg, rhs_reg)) ;
  
  // Free the previous result register.
  lreg->reset_use_for_expr_result();
  rreg->reset_use_for_expr_result();
  Code_For_Ast & rel_expr_code = *new Code_For_Ast(ic_list, result_reg);
  return rel_expr_code;

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

void Multiplication_Ast::print(ostream & file_buffer) {
  file_buffer << endl << AST_NODE_SPACE << "Arith: MULT" << endl;

  file_buffer << AST_SUB_NODE_SPACE << "LHS (";
  lhs->print(file_buffer);
  file_buffer << ")\n";
  
  file_buffer << AST_SUB_NODE_SPACE << "RHS (";
  rhs->print(file_buffer);
  file_buffer << ")";
}

Eval_Result & Multiplication_Ast::evaluate(Local_Environment & eval_env, ostream & file_buffer) {  
  Eval_Result & lhs_result = lhs->evaluate(eval_env, file_buffer);
  Eval_Result & rhs_result = rhs->evaluate(eval_env, file_buffer);
  
  if(node_data_type == int_data_type) {
    Eval_Result * result = new Eval_Result_Value_Int(); 
    if(lhs_result.get_result_enum() == int_result || lhs_result.get_result_enum() == bool_result) {
      result->set_value( lhs_result.get_int_value() * rhs_result.get_int_value());
    }
    else if(lhs_result.get_result_enum() == float_result) {
      result->set_value( (int) (lhs_result.get_value_float() * rhs_result.get_value_float()));
    }
    return * result;
  }
  
  else if(node_data_type == float_data_type) {
    Eval_Result * result = new Eval_Result_Value_Float(); 
    if(lhs_result.get_result_enum() == int_result || lhs_result.get_result_enum() == bool_result) {
      result->set_value_float( (float) (lhs_result.get_int_value() * rhs_result.get_int_value()));
    }
    else if(lhs_result.get_result_enum() == float_result) {
      result->set_value_float( lhs_result.get_value_float() * rhs_result.get_value_float());
    }
    return * result;
  }

  else {
    cout << "Data-Type not defined for addition\n";
  }
}

Code_For_Ast & Multiplication_Ast::compile() {
  CHECK_INVARIANT((lhs != NULL), "LHS cannot be null");
  CHECK_INVARIANT((rhs != NULL), "RHS cannot be null");
  
  Code_For_Ast & lhs_stmt = lhs->compile();
  Register_Descriptor * lreg = lhs_stmt.get_reg();
  Code_For_Ast & rhs_stmt = rhs->compile();
  Register_Descriptor * rreg = rhs_stmt.get_reg();

  CHECK_INVARIANT((lreg->get_value_type()==rreg->get_value_type()), 
                  "LHS and RHS are incompatible data types")

  list<Icode_Stmt *> & ic_list = *new list<Icode_Stmt *>;

  Ics_Opd * lhs_reg = new Register_Addr_Opd(lreg);
  Ics_Opd * rhs_reg = new Register_Addr_Opd(rreg);
  
  if (lhs_stmt.get_icode_list().empty() == false)
    ic_list = lhs_stmt.get_icode_list();
  if (rhs_stmt.get_icode_list().empty() == false)
    ic_list.splice(ic_list.end(), rhs_stmt.get_icode_list());
  
  Register_Descriptor * result_reg ;
  Tgt_Op opr ;
  if (lreg->get_value_type() == int_num) {
    result_reg = machine_dscr_object.get_new_register();
    opr = mul ;
  }
  if (lreg->get_value_type() == float_num) {
    result_reg = machine_dscr_object.get_new_float_register();
    opr = mul_d ;
  }
  result_reg->set_used_for_expr_result();
  Ics_Opd * register_result = new Register_Addr_Opd(result_reg);

  ic_list.push_back(new Compute_IC_Stmt(opr, register_result, lhs_reg, rhs_reg)) ;
  
  // Free the previous result register.
  lreg->reset_use_for_expr_result();
  lreg->clear_lra_symbol_list();
  rreg->reset_use_for_expr_result();
  rreg->clear_lra_symbol_list();
  Code_For_Ast & rel_expr_code = *new Code_For_Ast(ic_list, result_reg);
  return rel_expr_code;
}


Code_For_Ast & Multiplication_Ast::compile_and_optimize_ast(Lra_Outcome & lra) {
  CHECK_INVARIANT((lhs != NULL), "LHS cannot be null");
  CHECK_INVARIANT((rhs != NULL), "RHS cannot be null");
  
  Register_Descriptor * result_reg = NULL;
  
  lra.optimize_lra(mc_2r, NULL, lhs);
  Code_For_Ast & lhs_stmt = lhs->compile_and_optimize_ast(lra);
  Register_Descriptor * lreg = lhs_stmt.get_reg();

  lra.optimize_lra(mc_2r, NULL, rhs);
  Code_For_Ast & rhs_stmt = rhs->compile_and_optimize_ast(lra);
  Register_Descriptor * rreg = rhs_stmt.get_reg();

  list<Icode_Stmt *> & ic_list = *new list<Icode_Stmt *>;

  Ics_Opd * lhs_reg = new Register_Addr_Opd(lreg);
  Ics_Opd * rhs_reg = new Register_Addr_Opd(rreg);
  
  if (lhs_stmt.get_icode_list().empty() == false)
    ic_list = lhs_stmt.get_icode_list();
  if (rhs_stmt.get_icode_list().empty() == false)
    ic_list.splice(ic_list.end(), rhs_stmt.get_icode_list());
  
  Tgt_Op opr ;
  if (lreg->get_value_type() == int_num) {
    if (!result_reg) result_reg = machine_dscr_object.get_new_register();
    opr = mul ;
  }
  if (lreg->get_value_type() == float_num) {
    if(!result_reg) result_reg = machine_dscr_object.get_new_float_register();
    opr = mul_d ;
  }
  result_reg->set_used_for_expr_result();
  Ics_Opd * register_result = new Register_Addr_Opd(result_reg);

  ic_list.push_back(new Compute_IC_Stmt(opr, register_result, lhs_reg, rhs_reg)) ;
  
  // Free the previous result register.
  lreg->reset_use_for_expr_result();
  rreg->reset_use_for_expr_result();
  Code_For_Ast & rel_expr_code = *new Code_For_Ast(ic_list, result_reg);
  return rel_expr_code;

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

void Division_Ast::print(ostream & file_buffer) {
  file_buffer << endl << AST_NODE_SPACE << "Arith: DIV" << endl;

  file_buffer << AST_SUB_NODE_SPACE << "LHS (";
  lhs->print(file_buffer);
  file_buffer << ")\n";
  
  file_buffer << AST_SUB_NODE_SPACE << "RHS (";
  rhs->print(file_buffer);
  file_buffer << ")";
}

Eval_Result & Division_Ast::evaluate(Local_Environment & eval_env, ostream & file_buffer) {
  Eval_Result & lhs_result = lhs->evaluate(eval_env, file_buffer);
  Eval_Result & rhs_result = rhs->evaluate(eval_env, file_buffer);
  
  if(node_data_type == int_data_type) {
    Eval_Result * result = new Eval_Result_Value_Int();
    if(lhs_result.get_result_enum() == int_result || lhs_result.get_result_enum() == bool_result) {
      if(rhs_result.get_int_value() == 0) {
	cout << "Divide by 0";
      }
      result->set_value( lhs_result.get_int_value() / rhs_result.get_int_value());
    }
    else if(lhs_result.get_result_enum() == float_result) {
      if(rhs_result.get_value_float() == 0) {
	cout << "Divide by 0";
      }
      result->set_value( (int) (lhs_result.get_value_float() / rhs_result.get_value_float()));
    }
    return * result;
  }
  
  else if(node_data_type == float_data_type) {
    Eval_Result * result = new Eval_Result_Value_Float(); 
    if(lhs_result.get_result_enum() == int_result || lhs_result.get_result_enum() == bool_result) {
      if(rhs_result.get_int_value() == 0) {
	cout << "Divide by 0";
      }
      result->set_value_float( (float) (lhs_result.get_int_value() / rhs_result.get_int_value()));
    }
    else if(lhs_result.get_result_enum() == float_result) { 
      if(rhs_result.get_value_float() == 0) {
	cout << "Divide by 0";
      }
      result->set_value_float( lhs_result.get_value_float() / rhs_result.get_value_float());
    }
    return * result;
  }

  else {
    cout << "Data-Type not defined for addition\n";
  }
}
Code_For_Ast & Division_Ast::compile() {
  CHECK_INVARIANT((lhs != NULL), "LHS cannot be null");
  CHECK_INVARIANT((rhs != NULL), "RHS cannot be null");
  
  Code_For_Ast & lhs_stmt = lhs->compile();
  Register_Descriptor * lreg = lhs_stmt.get_reg();
  Code_For_Ast & rhs_stmt = rhs->compile();
  Register_Descriptor * rreg = rhs_stmt.get_reg();

  CHECK_INVARIANT((lreg->get_value_type()==rreg->get_value_type()), 
                  "LHS and RHS are incompatible data types")

  list<Icode_Stmt *> & ic_list = *new list<Icode_Stmt *>;

  Ics_Opd * lhs_reg = new Register_Addr_Opd(lreg);
  Ics_Opd * rhs_reg = new Register_Addr_Opd(rreg);
  
  if (lhs_stmt.get_icode_list().empty() == false)
    ic_list = lhs_stmt.get_icode_list();
  if (rhs_stmt.get_icode_list().empty() == false)
    ic_list.splice(ic_list.end(), rhs_stmt.get_icode_list());
  
  Register_Descriptor * result_reg ;
  Tgt_Op opr ;
  if (lreg->get_value_type() == int_num) {
    result_reg = machine_dscr_object.get_new_register();
    opr = divide ;
  }
  if (lreg->get_value_type() == float_num) {
    result_reg = machine_dscr_object.get_new_float_register();
    opr = divide_d ;
  }
  result_reg->set_used_for_expr_result();
  Ics_Opd * register_result = new Register_Addr_Opd(result_reg);

  ic_list.push_back(new Compute_IC_Stmt(opr, register_result, lhs_reg, rhs_reg)) ;
  
  // Free the previous result register.
  lreg->reset_use_for_expr_result();
  lreg->clear_lra_symbol_list();
  rreg->reset_use_for_expr_result();
  rreg->clear_lra_symbol_list();
  Code_For_Ast & rel_expr_code = *new Code_For_Ast(ic_list, result_reg);
  return rel_expr_code;
}
Code_For_Ast & Division_Ast::compile_and_optimize_ast(Lra_Outcome & lra) {
  CHECK_INVARIANT((lhs != NULL), "LHS cannot be null");
  CHECK_INVARIANT((rhs != NULL), "RHS cannot be null");
  
  Register_Descriptor * result_reg = NULL;
  
  lra.optimize_lra(mc_2r, NULL, lhs);
  Code_For_Ast & lhs_stmt = lhs->compile_and_optimize_ast(lra);
  Register_Descriptor * lreg = lhs_stmt.get_reg();

  lra.optimize_lra(mc_2r, NULL, rhs);
  Code_For_Ast & rhs_stmt = rhs->compile_and_optimize_ast(lra);
  Register_Descriptor * rreg = rhs_stmt.get_reg();

  list<Icode_Stmt *> & ic_list = *new list<Icode_Stmt *>;

  Ics_Opd * lhs_reg = new Register_Addr_Opd(lreg);
  Ics_Opd * rhs_reg = new Register_Addr_Opd(rreg);
  
  if (lhs_stmt.get_icode_list().empty() == false)
    ic_list = lhs_stmt.get_icode_list();
  if (rhs_stmt.get_icode_list().empty() == false)
    ic_list.splice(ic_list.end(), rhs_stmt.get_icode_list());
  
  Tgt_Op opr ;
  if (lreg->get_value_type() == int_num) {
    if (!result_reg) result_reg = machine_dscr_object.get_new_register();
    opr = divide ;
  }
  if (lreg->get_value_type() == float_num) {
    if(!result_reg) result_reg = machine_dscr_object.get_new_float_register();
    opr = divide_d ;
  }
  result_reg->set_used_for_expr_result();
  Ics_Opd * register_result = new Register_Addr_Opd(result_reg);

  ic_list.push_back(new Compute_IC_Stmt(opr, register_result, lhs_reg, rhs_reg)) ;
  
  // Free the previous result register.
  lreg->reset_use_for_expr_result();
  rreg->reset_use_for_expr_result();
  Code_For_Ast & rel_expr_code = *new Code_For_Ast(ic_list, result_reg);
  return rel_expr_code;

}
/**********************************************************************************/

Unary_Ast::Unary_Ast(Ast * r) {
  lhs = NULL;
  rhs = r;
}

Unary_Ast::~Unary_Ast() {}

bool Unary_Ast::check_ast() {
  if(rhs->get_data_type() == int_data_type || rhs->get_data_type() == float_data_type ){
    node_data_type = rhs->get_data_type();
    return true;
  }
  cout << "Unary expression data type not compatible";
}


Data_Type Unary_Ast::get_data_type() {
  return node_data_type;
}

void Unary_Ast::print(ostream & file_buffer) {
  file_buffer << endl << AST_NODE_SPACE << "Arith: UMINUS" << endl;
  file_buffer << AST_SUB_NODE_SPACE << "LHS (";
  rhs->print(file_buffer);
  file_buffer << ")";
}

Eval_Result & Unary_Ast::evaluate(Local_Environment & eval_env, ostream & file_buffer) {
  Eval_Result & rhs_result = rhs->evaluate(eval_env, file_buffer);
  
  if(node_data_type == int_data_type) {
    Eval_Result * result = new Eval_Result_Value_Int(); 
    if(rhs_result.get_result_enum() == int_result || rhs_result.get_result_enum() == bool_result) {
      result->set_value( -1 * rhs_result.get_int_value());
    }
    else if(rhs_result.get_result_enum() == float_result) {
      result->set_value(-1 * (int) rhs_result.get_value_float());
    }
    return * result;
  }
  
  else if(node_data_type == float_data_type) {
    Eval_Result * result = new Eval_Result_Value_Float(); 
    if(rhs_result.get_result_enum() == int_result || rhs_result.get_result_enum() == bool_result) {
      result->set_value_float(-1 * (float) rhs_result.get_int_value());
    }
    else if(rhs_result.get_result_enum() == float_result) {
      result->set_value_float( -1 * rhs_result.get_value_float());
    }
    return * result;
  }

  else {
    cout << "Data-Type not defined for addition\n";
  }  
}
Code_For_Ast & Unary_Ast::compile() {
  CHECK_INVARIANT((rhs != NULL), "RHS cannot be null");
  
  Code_For_Ast & rhs_stmt = rhs->compile();
  Register_Descriptor * rreg = rhs_stmt.get_reg();

  list<Icode_Stmt *> & ic_list = *new list<Icode_Stmt *>;

  Ics_Opd * rhs_reg = new Register_Addr_Opd(rreg);
  
  if (rhs_stmt.get_icode_list().empty() == false)
    ic_list = rhs_stmt.get_icode_list();
  
  Register_Descriptor * result_reg ;
  Tgt_Op opr ;
  if (rreg->get_value_type() == int_num) {
    result_reg = machine_dscr_object.get_new_register();
    opr = neg ;
  }
  if (rreg->get_value_type() == float_num) {
    result_reg = machine_dscr_object.get_new_float_register();
    opr = neg_d ;
  }
  result_reg->set_used_for_expr_result();
  Ics_Opd * register_result = new Register_Addr_Opd(result_reg);

  ic_list.push_back(new Unary_IC_Stmt(opr, register_result, rhs_reg)) ;
  
  // Free the previous result register.
  rreg->reset_use_for_expr_result();
  rreg->clear_lra_symbol_list();
  Code_For_Ast & rel_expr_code = *new Code_For_Ast(ic_list, result_reg);
  return rel_expr_code;
}

Code_For_Ast & Unary_Ast::compile_and_optimize_ast(Lra_Outcome & lra) {
  CHECK_INVARIANT((rhs != NULL), "RHS cannot be null");
  
  Register_Descriptor * result_reg = NULL;
  
  lra.optimize_lra(mc_2r, NULL, rhs);
  Code_For_Ast & rhs_stmt = rhs->compile_and_optimize_ast(lra);
  Register_Descriptor * rreg = rhs_stmt.get_reg();

  list<Icode_Stmt *> & ic_list = *new list<Icode_Stmt *>;

  Ics_Opd * rhs_reg = new Register_Addr_Opd(rreg);
  
  if (rhs_stmt.get_icode_list().empty() == false)
    ic_list = rhs_stmt.get_icode_list();
  
  Tgt_Op opr ;
  if (rreg->get_value_type() == int_num) {
    if (!result_reg) result_reg = machine_dscr_object.get_new_register();
    opr = neg ;
  }
  if (rreg->get_value_type() == float_num) {
    if(!result_reg) result_reg = machine_dscr_object.get_new_float_register();
    opr = neg_d ;
  }
  result_reg->set_used_for_expr_result();
  Ics_Opd * register_result = new Register_Addr_Opd(result_reg);

  ic_list.push_back(new Unary_IC_Stmt(opr, register_result, rhs_reg)) ;
  
  // Free the previous result register.
  rreg->reset_use_for_expr_result();
  Code_For_Ast & rel_expr_code = *new Code_For_Ast(ic_list, result_reg);
  return rel_expr_code;

}
/***********************************************************************************/

/**********************************************************************************/

Type_Cast_Ast::Type_Cast_Ast(Ast * r, Data_Type dt) {
  lhs = NULL;
  rhs = r;
  node_data_type = dt ;
}

Type_Cast_Ast::~Type_Cast_Ast() {}

bool Type_Cast_Ast::check_ast() {
  if(rhs->get_data_type() == int_data_type || rhs->get_data_type() == float_data_type ){
    //node_data_type = rhs->get_data_type();
    return true;
  }
  cout << "Unary expression data type not compatible";
}


Data_Type Type_Cast_Ast::get_data_type() {
  return node_data_type;
}

void Type_Cast_Ast::print(ostream& file_buffer) {
  if (rhs) rhs->print(file_buffer) ;
}

Eval_Result & Type_Cast_Ast::evaluate(Local_Environment & eval_env, ostream & file_buffer) {
  Eval_Result & rhs_result = rhs->evaluate(eval_env, file_buffer);
  
  if(node_data_type == int_data_type) {
    if(rhs_result.get_result_enum() == int_result || rhs_result.get_result_enum() == bool_result) {
      return rhs_result;
    }
    else if(rhs_result.get_result_enum() == float_result) {
      Eval_Result * result = new Eval_Result_Value_Int(); 
      result->set_value((int) rhs_result.get_value_float());
      return * result;
    }
  }
  else if(node_data_type == float_data_type) {
    if(rhs_result.get_result_enum() == int_result || rhs_result.get_result_enum() == bool_result) {
      Eval_Result * result = new Eval_Result_Value_Float(); 
      result->set_value_float((float) rhs_result.get_int_value());
      return * result;
    }
    else if(rhs_result.get_result_enum() == float_result) {
      return rhs_result ;
    }
  }
  else {
    cout << "Data-Type not defined for addition\n";
  }  
}


Code_For_Ast & Type_Cast_Ast::compile() {
  CHECK_INVARIANT((rhs != NULL), "RHS cannot be null");
  
  Code_For_Ast & rhs_stmt = rhs->compile();
  Register_Descriptor * rreg = rhs_stmt.get_reg();

  if ((rreg->get_value_type() == int_num && node_data_type==int_data_type) ||
      (rreg->get_value_type() == float_num && node_data_type==float_data_type) )
  {
    return rhs_stmt ;
  }

  else {
    list<Icode_Stmt *> & ic_list = *new list<Icode_Stmt *>;

    Ics_Opd * rhs_reg = new Register_Addr_Opd(rreg);
    
    if (rhs_stmt.get_icode_list().empty() == false)
      ic_list = rhs_stmt.get_icode_list();
    
    Register_Descriptor * result_reg ;
    Tgt_Op opr ;

    if (rreg->get_value_type() == int_num && node_data_type==float_data_type) {
      result_reg = machine_dscr_object.get_new_float_register();
      opr = cast_float ;
    }
    else if (rreg->get_value_type() == float_num && node_data_type==int_data_type) {
      result_reg = machine_dscr_object.get_new_register();
      opr = cast_int ;
    }
    else {
      CHECK_INVARIANT(false, "Invalid cast") ;
    }
    result_reg->set_used_for_expr_result();
    Ics_Opd * register_result = new Register_Addr_Opd(result_reg);

    ic_list.push_back(new Unary_IC_Stmt(opr, register_result, rhs_reg)) ;
    
    // Free the previous result register.
    rreg->reset_use_for_expr_result();
    rreg->clear_lra_symbol_list();
    Code_For_Ast & rel_expr_code = *new Code_For_Ast(ic_list, result_reg);
    return rel_expr_code;
  }
}

Code_For_Ast & Type_Cast_Ast::compile_and_optimize_ast(Lra_Outcome & lra) {
  CHECK_INVARIANT((rhs != NULL), "RHS cannot be null");
  
  Register_Descriptor * result_reg = NULL;
  
  lra.optimize_lra(mc_2r, NULL, rhs);
  Code_For_Ast & rhs_stmt = rhs->compile_and_optimize_ast(lra);
  Register_Descriptor * rreg = rhs_stmt.get_reg();

  if ((rreg->get_value_type() == int_num && node_data_type==int_data_type) ||
      (rreg->get_value_type() == float_num && node_data_type==float_data_type) )
  {
    return rhs_stmt ;
  }

  list<Icode_Stmt *> & ic_list = *new list<Icode_Stmt *>;;

  Ics_Opd * rhs_reg = new Register_Addr_Opd(rreg);
  
  if (rhs_stmt.get_icode_list().empty() == false)
    ic_list = rhs_stmt.get_icode_list();
  
  Tgt_Op opr ;
  if (rreg->get_value_type() == int_num && node_data_type==float_data_type) {
    if (!result_reg) result_reg = machine_dscr_object.get_new_float_register();
    opr = cast_float ;
  }
  else if (rreg->get_value_type() == float_num && node_data_type==int_data_type) {
    if (!result_reg) result_reg = machine_dscr_object.get_new_register();
    opr = cast_int ;
  }
  else {
    CHECK_INVARIANT(false, "Invalid cast") ;
  }
  result_reg->set_used_for_expr_result();
  Ics_Opd * register_result = new Register_Addr_Opd(result_reg);

  ic_list.push_back(new Unary_IC_Stmt(opr, register_result, rhs_reg)) ;
  
  // Free the previous result register.
  rreg->reset_use_for_expr_result();
  Code_For_Ast & rel_expr_code = *new Code_For_Ast(ic_list, result_reg);
  return rel_expr_code;

}
/***********************************************************************************/

#if 0
Call_Ast::Call_Ast() {
}

Call_Ast::Call_Ast(Procedure * f, list<Ast *> args) {
  fn = f;
  arguments = args;
  node_data_type = void_data_type;
}

Call_Ast::Call_Ast(Procedure * f) {
  fn = f;
  arguments =  *(new list<Ast *>());  
  node_data_type = void_data_type;
}


Data_Type Call_Ast::get_data_type() {
  return node_data_type;
}

Call_Ast::~Call_Ast() {}

void Call_Ast::print(ostream & file_buffer) {
	file_buffer << endl << AST_SPACE << "FN CALL: " << fn->get_proc_name() << "(" ;
	list<Ast *>::iterator itr_arg;
	for(itr_arg = arguments.begin(); itr_arg != arguments.end() ; itr_arg++) {
		file_buffer << endl;
		file_buffer << AST_SUB_NODE_SPACE;
		(*itr_arg)->print(file_buffer);
	}
	file_buffer << ")";
}

bool Call_Ast::check_ast(int line) {
	node_data_type = fn->get_return_type();
	bool check = fn->check_argument_types(arguments);
	if(check == false) {
		report_error("Arguments type is not same as declaration in " + fn->get_proc_name(), line);
	}
	return check;
}

Eval_Result & Call_Ast::evaluate(Local_Environment & eval_env, ostream & file_buffer){
  Eval_Result * res;
	if(arguments.size() == 0) {
		/* Function call with no arguments */
		res = &fn->evaluate(file_buffer);
	}
	else {
		list<Eval_Result*> argument_val_list;
		
		list<Ast *>::iterator itr_arg;
		for(itr_arg = arguments.begin(); itr_arg != arguments.end() ; itr_arg++) {
			Eval_Result & result = (*itr_arg)->evaluate(eval_env, file_buffer);
			argument_val_list.push_back(&result);
			
		}
		/* Function call with arguments */
		res = &fn->evaluate(argument_val_list, file_buffer);	
	}
	if(node_data_type == int_data_type) {
		Eval_Result * result = new Eval_Result_Value_Int(); 
		if(res->get_result_enum() == int_result || res->get_result_enum() == bool_result) {
			result->set_value(res->get_int_value());
		}
		else if(res->get_result_enum() == float_result) {
			result->set_value((int) res->get_value_float());
		}
		return * result;
	}
  
	else if(node_data_type == float_data_type) {
		Eval_Result * result = new Eval_Result_Value_Float(); 
		if(res->get_result_enum() == int_result || res->get_result_enum() == bool_result) {
			result->set_value_float((float) res->get_int_value());
		}
		else if(res->get_result_enum() == float_result) {
			result->set_value_float(res->get_value_float());
		}
		return * result;
	}
	else if(node_data_type == void_data_type) {
		return * res;
	}
	else {
		report_error("Data-Type not defined for return type\n", NOLINE);
	}  	
}
#endif
