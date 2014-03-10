
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

#include<string>
#include<fstream>
#include<iostream>
#include <iomanip>

using namespace std;

#include"error-display.hh"
#include"local-environment.hh"

#include"symbol-table.hh"
#include"ast.hh"
#include"basic-block.hh"
#include"procedure.hh"
#include"program.hh"

Procedure::Procedure(Data_Type proc_return_type, string proc_name)
{
	return_type = proc_return_type;
	name = proc_name;
}

Procedure::~Procedure()
{
	list<Basic_Block *>::iterator i;
	for (i = basic_block_list.begin(); i != basic_block_list.end(); i++)
		delete (*i);
}

string Procedure::get_proc_name()
{
	return name;
}

void Procedure::set_basic_block_list(list<Basic_Block *> bb_list)
{
	basic_block_list = bb_list;
}

void Procedure::set_local_list(Symbol_Table & new_list)
{
	local_symbol_table = new_list;
	local_symbol_table.set_table_scope(local);
}

void Procedure::set_argument_list(Symbol_Table & arg_list)
{
	argument_symbol_table = arg_list;
	argument_symbol_table.set_table_scope(local);
}

Data_Type Procedure::get_return_type()
{
	return return_type;
}

bool Procedure::variable_in_symbol_list_check(string variable)
{
	return (local_symbol_table.variable_in_symbol_list_check(variable) || 
		argument_symbol_table.variable_in_symbol_list_check(variable));
}

Symbol_Table_Entry & Procedure::get_symbol_table_entry(string variable_name)
{
	if(local_symbol_table.variable_in_symbol_list_check(variable_name)) {
		return local_symbol_table.get_symbol_table_entry(variable_name);
	}
	else if(argument_symbol_table.variable_in_symbol_list_check(variable_name)) {
		return argument_symbol_table.get_symbol_table_entry(variable_name);
	}
}

bool Procedure::check_argument_types(list<Ast *> & arg_types) {
	bool check = argument_symbol_table.check_ordered_data_types(arg_types);
	if(check == false) {
		report_error("Function " + name + " usage does not match declaration", NOLINE);
	}
	return check;
}
	


void Procedure::print_ast(ostream & file_buffer)
{
	file_buffer << PROC_SPACE << "Procedure: " << name << "\n\n";

	list<Basic_Block *>::iterator i;
	for(i = basic_block_list.begin(); i != basic_block_list.end(); i++)
		(*i)->print_bb(file_buffer);
}
	
Basic_Block & Procedure::get_start_basic_block()
{
	list<Basic_Block *>::iterator i;
	i = basic_block_list.begin();
	return **i;
}

Basic_Block * Procedure::get_next_bb(Basic_Block & current_bb)
{
	bool flag = false;

	list<Basic_Block *>::iterator i;
	for(i = basic_block_list.begin(); i != basic_block_list.end(); i++)
	{
		if((*i)->get_bb_number() == current_bb.get_bb_number())
		{
			flag = true;
			continue;
		}
		if (flag)
			return (*i);
	}
	
	return NULL;
}

Basic_Block * Procedure::get_next_bb(int bb_no) 
{
  list<Basic_Block *>::iterator i;
  for(i = basic_block_list.begin(); i != basic_block_list.end(); i++) {
    if((*i)->get_bb_number() == bb_no) {
      return (*i);
    }
  }
  // BB No does not exist. Report Error.
  char err_msg[30];
  sprintf(err_msg, "bb %d doesn't exist\n", bb_no);
  report_error(err_msg, NOLINE);
}


Eval_Result & Procedure::evaluate(ostream & file_buffer)
{
	Local_Environment & eval_env = *new Local_Environment();
	local_symbol_table.create(eval_env);
	Eval_Result * result = NULL;
	file_buffer << PROC_SPACE << "Evaluating Procedure << " << name << " >>\n";
	file_buffer << LOC_VAR_SPACE << "Local Variables (before evaluating):\n";
	eval_env.print(file_buffer);
	file_buffer << "\n";
	
	Basic_Block * current_bb = &(get_start_basic_block());
	while (current_bb)
	{
	  result = &(current_bb->evaluate(eval_env, file_buffer));
	  if(result->get_result_enum() == return_result) {
		  
		  if(result->get_return_result() != NULL) {
			  result = result->get_return_result();
		  }
		  break;
	  }
	  if( result->get_result_enum() == bb_result ) {
		  current_bb = get_next_bb(result->get_value()); 
	  }
	  else {
	    current_bb = get_next_bb(*current_bb);	
	  }	
	}

	file_buffer << "\n\n";
	file_buffer << LOC_VAR_SPACE << "Local Variables (after evaluating) Function: << " << name << " >>\n";
	eval_env.print(file_buffer);
	if(result->get_result_enum() == int_result || result->get_result_enum() == bool_result) {
		file_buffer << VAR_SPACE << "return : " << result->get_value() << endl;
	}
	else if(result->get_result_enum() == float_result) {
		file_buffer << VAR_SPACE << "return : " << std::fixed << std::setprecision(2) << result->get_value_float() << endl;
	}
	
	// cout << result->get_result_enum() << " is the Result type\n";
	return *result;
}
	
Eval_Result & Procedure::evaluate(list<Eval_Result *> & argument_value_list, ostream & file_buffer)
{
   	
	Local_Environment & eval_env = *new Local_Environment();
	local_symbol_table.create(eval_env);
	
	// Add return variable in return symbol table.
	string *return_name = new string("return");
	Symbol_Table * return_symbol_table;
	if(return_type == int_data_type) {
		return_symbol_table = new Symbol_Table();
		return_symbol_table->push_symbol(new Symbol_Table_Entry(*return_name, int_data_type));
	}
	else if(return_type == float_data_type) {
		return_symbol_table = new Symbol_Table();
		return_symbol_table->push_symbol(new Symbol_Table_Entry(*return_name, float_data_type));
	}

	argument_symbol_table.create(eval_env);
	
	list<Symbol_Table_Entry *>::iterator arg_itr = argument_symbol_table.get_symbol_table_iterator();
	list<Eval_Result *>::iterator val_itr = argument_value_list.begin();
	for(; val_itr != argument_value_list.end() ; val_itr++, arg_itr++) {
		eval_env.put_variable_value( *((Eval_Result_Value *) (*val_itr)), (*arg_itr)->get_variable_name()); 
	}
	Eval_Result * result = NULL;

	file_buffer << endl << PROC_SPACE << "Evaluating Procedure << " << name << " >>\n";
	file_buffer << LOC_VAR_SPACE << "Local Variables (before evaluating):\n";
	eval_env.print(file_buffer);
	file_buffer << "\n";
	
	Basic_Block * current_bb = &(get_start_basic_block());
	while (current_bb)
	{
	  result = &(current_bb->evaluate(eval_env, file_buffer));
	  if(result->get_result_enum() == return_result) {
		  
		  if(result->get_return_result() != NULL) {
			  result = result->get_return_result();
		  }
		  else {
			  // Dummy Result.
			  result = new Eval_Result_Value_Int();
			  result->set_result_enum(void_result);
		  }
		  break;
	  }
	  if( result->get_result_enum() == bb_result ) {
		  current_bb = get_next_bb(result->get_value()); 
	  }
	  else {
	    current_bb = get_next_bb(*current_bb);	
	  }	
	}

	file_buffer << "\n\n";
	file_buffer << LOC_VAR_SPACE << "Local Variables (after evaluating) Function: << " << name << " >>\n";
	
	if(return_type == int_data_type || return_type == float_data_type) {
		if(result->get_result_enum() != return_result && result->get_result_enum() != void_result ) {
			return_symbol_table->create(eval_env);
			eval_env.put_variable_value( *((Eval_Result_Value *)result), *return_name);
		}
	}
	eval_env.print(file_buffer);
	/*
	if(result->get_result_enum() == int_result || result->get_result_enum() == bool_result) {
		file_buffer << VAR_SPACE << "return : " << result->get_value() << endl;
	}
	else if(result->get_result_enum() == float_result) {
		file_buffer << VAR_SPACE << "return : " << std::fixed << std::setprecision(2) << result->get_value_float() << endl;
	}
	*/
	// cout << result->get_result_enum() << " is the Result type\n";
	return *result;
}

