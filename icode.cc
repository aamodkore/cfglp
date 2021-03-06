
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
#include <sstream>
#include <string>
#include <vector>
#include <list>
#include <map>

using namespace std;

#include "common-classes.hh"
#include "error-display.hh"
#include "local-environment.hh"
#include "icode.hh"
#include "reg-alloc.hh"
#include "symbol-table.hh"
#include "ast.hh"
#include "procedure.hh"
#include "program.hh"

/****************************** Class Ics_Opd *****************************/

Opd_Category Ics_Opd::get_opd_category() 
{ 
	return type;
} 

Register_Descriptor * Ics_Opd::get_reg()
{
	CHECK_INVARIANT(CONTROL_SHOULD_NOT_REACH, 
		"The get_Reg method should not be called for a non-reg operand");
}

Symbol_Table_Entry & Ics_Opd::get_symbol_entry() 
{
	CHECK_INVARIANT(CONTROL_SHOULD_NOT_REACH, 
		"The get_Sym_Entry method should not be called for a non-address operand");
}

/****************************** Class Mem_Addr_Opd *****************************/

Mem_Addr_Opd::Mem_Addr_Opd(Symbol_Table_Entry & se) 
{
	symbol_entry = &se;
	type = memory_addr;
}

Mem_Addr_Opd & Mem_Addr_Opd::operator=(const Mem_Addr_Opd & rhs)
{
	type = rhs.type;
	symbol_entry = rhs.symbol_entry;

	return *this;
}

void Mem_Addr_Opd::print_ics_opd(ostream & file_buffer) 
{
	string name = symbol_entry->get_variable_name();

	file_buffer << name;
}

void Mem_Addr_Opd::print_asm_opd(ostream & file_buffer) 
{
	Table_Scope symbol_scope = symbol_entry->get_symbol_scope();

	CHECK_INVARIANT(((symbol_scope == local) || (symbol_scope == global)), 
			"Wrong scope value");

	if (symbol_scope == local)
	{
		int offset = symbol_entry->get_start_offset();
		file_buffer << -offset << "($fp)";
	}
	else
		file_buffer << symbol_entry->get_variable_name();
}

/****************************** Class Register_Addr_Opd *****************************/

Register_Addr_Opd::Register_Addr_Opd(Register_Descriptor * reg) 
{
	type = register_addr;
	register_description = reg;
}

Register_Descriptor * Register_Addr_Opd::get_reg()    { return register_description; }

Register_Addr_Opd& Register_Addr_Opd::operator=(const Register_Addr_Opd& rhs)
{
	type = rhs.type;     
	register_description = rhs.register_description ;

	return *this;
}

void Register_Addr_Opd::print_ics_opd(ostream & file_buffer) 
{
	CHECK_INVARIANT((register_description != NULL), "Register cannot be null");

	string name = register_description->get_name();

	file_buffer << name;
}

void Register_Addr_Opd::print_asm_opd(ostream & file_buffer) 
{
	CHECK_INVARIANT((register_description != NULL), "Register cannot be null");

	string name = register_description->get_name();

	file_buffer << "$" << name;
}

/****************************** Class Const_Opd *****************************/

template <class DATA_TYPE>
Const_Opd<DATA_TYPE>::Const_Opd(DATA_TYPE n) 
{
	type = constant_addr;
	constant_type = int_data_type ;
	num = n;
}

template <class DATA_TYPE>
Const_Opd<DATA_TYPE>::Const_Opd(Data_Type dt, DATA_TYPE n) 
{
	type = constant_addr;
	constant_type = dt ;
	num = n;
}

template <class DATA_TYPE>
Const_Opd<DATA_TYPE> & Const_Opd<DATA_TYPE>::operator=(const Const_Opd<DATA_TYPE> & rhs)
{
	type = rhs.type;
	num = rhs.num;

	return *this;
}

template <class DATA_TYPE>
void Const_Opd<DATA_TYPE>::print_ics_opd(ostream & file_buffer) 
{
	if (constant_type == float_data_type) {
		file_buffer << std::fixed << setprecision(2) << num;
	} else {
		file_buffer << num ;
	}
}

template <class DATA_TYPE>
void Const_Opd<DATA_TYPE>::print_asm_opd(ostream & file_buffer) 
{
	if (constant_type == float_data_type) {
		file_buffer << std::fixed << setprecision(2) << num;
	} else {
		file_buffer << num;
	}
}

/****************************** Class Icode_Stmt *****************************/

Instruction_Descriptor & Icode_Stmt::get_op()
{ 
	return op_desc; 
}

Ics_Opd * Icode_Stmt::get_opd1()
{
	CHECK_INVARIANT(CONTROL_SHOULD_NOT_REACH, "virtual method get_Opd1 not implemented");
}

Ics_Opd * Icode_Stmt::get_opd2()
{
	CHECK_INVARIANT(CONTROL_SHOULD_NOT_REACH, "virtual method get_Opd2 not implemented");
}

Ics_Opd * Icode_Stmt::get_result()
{
	CHECK_INVARIANT(CONTROL_SHOULD_NOT_REACH, "virtual method get_Result not implemented");
}

void Icode_Stmt::set_opd1(Ics_Opd * ics_opd)
{
	CHECK_INVARIANT(CONTROL_SHOULD_NOT_REACH, "virtual method set_Opd1 not implemented");
}

void Icode_Stmt::set_opd2(Ics_Opd * ics_opd)
{
	CHECK_INVARIANT(CONTROL_SHOULD_NOT_REACH, "virtual method set_Opd2 not implemented");
}

void Icode_Stmt::set_result(Ics_Opd * ics_opd)
{
	CHECK_INVARIANT(CONTROL_SHOULD_NOT_REACH, "virtual methos set_Result not implemented");
}

/*************************** Class Move_IC_Stmt *****************************/

Move_IC_Stmt::Move_IC_Stmt(Tgt_Op op, Ics_Opd * o1, Ics_Opd * res)
{
	CHECK_INVARIANT((machine_dscr_object.spim_instruction_table[op] != NULL),
			"Instruction description in spim table cannot be null");

	op_desc = *(machine_dscr_object.spim_instruction_table[op]);
	opd1 = o1;   
	result = res; 
}

Ics_Opd * Move_IC_Stmt::get_opd1()          { return opd1; }
Ics_Opd * Move_IC_Stmt::get_result()        { return result; }

void Move_IC_Stmt::set_opd1(Ics_Opd * io)   { opd1 = io; }
void Move_IC_Stmt::set_result(Ics_Opd * io) { result = io; }

Move_IC_Stmt& Move_IC_Stmt::operator=(const Move_IC_Stmt& rhs)
{
	op_desc = rhs.op_desc;
	opd1 = rhs.opd1;
	result = rhs.result; 

	return *this;
}

void Move_IC_Stmt::print_icode(ostream & file_buffer)
{
	CHECK_INVARIANT (opd1, "Opd1 cannot be NULL for a move IC Stmt");
	CHECK_INVARIANT (result, "Result cannot be NULL for a move IC Stmt");

	string operation_name = op_desc.get_name();

	Icode_Format ic_format = op_desc.get_ic_format();

	switch (ic_format)
	{
	case i_r_op_o1: 
			file_buffer << "\t" << operation_name ;
			if (operation_name.size()<7) 
				file_buffer << ":\t\t";
			else if (operation_name.size()<15)
				file_buffer << ":\t";
			else
				file_buffer << ":";
			result->print_ics_opd(file_buffer);
			file_buffer << " <- ";
			opd1->print_ics_opd(file_buffer);
			file_buffer << "\n";

			break; 

	default: CHECK_INVARIANT(CONTROL_SHOULD_NOT_REACH, 
				"Intermediate code format not supported");
		break;
	}
}

void Move_IC_Stmt::print_assembly(ostream & file_buffer)
{
	CHECK_INVARIANT (opd1, "Opd1 cannot be NULL for a move IC Stmt");
	CHECK_INVARIANT (result, "Result cannot be NULL for a move IC Stmt");
	string op_name = op_desc.get_mnemonic();

	Assembly_Format assem_format = op_desc.get_assembly_format();
	switch (assem_format)
	{
	case a_op_r_o1: 
			file_buffer << "\t" << op_name << " ";
			result->print_asm_opd(file_buffer);
			file_buffer << ", ";
			opd1->print_asm_opd(file_buffer);
			file_buffer << "\n";

			break; 

	case a_op_o1_r: 
	  file_buffer << "\t" << op_name << " ";
			opd1->print_asm_opd(file_buffer);
			file_buffer << ", ";
			result->print_asm_opd(file_buffer);
			file_buffer << "\n";

			break; 

	default: CHECK_INVARIANT(CONTROL_SHOULD_NOT_REACH, "Intermediate code format not supported");
		break;
	}
}
/******************************* Class Label_IC_Stmt ***************************/
Label_IC_Stmt::Label_IC_Stmt() {
	label_no = 0;
}

Label_IC_Stmt::Label_IC_Stmt(int no){
	label_no = no;
	CHECK_INVARIANT((machine_dscr_object.spim_instruction_table[label] != NULL),
			"Instruction description in spim table cannot be null");

	op_desc = *(machine_dscr_object.spim_instruction_table[label]);
}

Label_IC_Stmt::~Label_IC_Stmt() 
{}


Instruction_Descriptor & Label_IC_Stmt::get_inst_op_of_ics() {}

void Label_IC_Stmt::print_icode(ostream & file_buffer) {
	Icode_Format ic_format = op_desc.get_ic_format();
	string operation_name = op_desc.get_name();
	switch (ic_format)
	{
	case i_label: 
		file_buffer << "\n" << operation_name << label_no << ":";
		file_buffer << "\n";
		break; 

	default: CHECK_INVARIANT(CONTROL_SHOULD_NOT_REACH, 
				"Intermediate code format not supported");
		break;
	}
}

void Label_IC_Stmt::print_assembly(ostream & file_buffer) {
	string op_name = op_desc.get_mnemonic();
	
	Assembly_Format assem_format = op_desc.get_assembly_format();
	switch (assem_format)
	{
	case a_label: 
		file_buffer << "\n" << op_name << label_no <<  ":";
		file_buffer << "\n";
		break; 

	default: CHECK_INVARIANT(CONTROL_SHOULD_NOT_REACH, "Intermediate code format not supported");
		break;
	}
}

/******************************* Class Control_Flow_IC_Stmt ***********************/
Control_Flow_IC_Stmt::Control_Flow_IC_Stmt() {
	label_name = "";
	offset = 0 ;
}
Control_Flow_IC_Stmt::Control_Flow_IC_Stmt(int no) {
	offset = 0 ;
	stringstream label_str ;
	label_str << "label" << no ;
	label_name = label_str.str();
	CHECK_INVARIANT((machine_dscr_object.spim_instruction_table[jump] != NULL),
			"Instruction description in spim table cannot be null");

	op_desc = *(machine_dscr_object.spim_instruction_table[jump]);
}

Control_Flow_IC_Stmt::Control_Flow_IC_Stmt(Tgt_Op op, string name, int off) {
	label_name = name;
	offset = off ;
	CHECK_INVARIANT((machine_dscr_object.spim_instruction_table[op] != NULL),
			"Instruction description in spim table cannot be null");

	op_desc = *(machine_dscr_object.spim_instruction_table[op]);
}

Control_Flow_IC_Stmt::Control_Flow_IC_Stmt(Tgt_Op op, Ics_Opd * opd1, Ics_Opd * opd2, int no) {
	stringstream label_str ;
	offset = 0 ;
	label_str << "label" << no ;
	label_name = label_str.str();
	CHECK_INVARIANT((machine_dscr_object.spim_instruction_table[op] != NULL),
			"Instruction description in spim table cannot be null");

	op_desc = *(machine_dscr_object.spim_instruction_table[op]);
	l_opd = opd1;
	r_opd = opd2;
}
	
Control_Flow_IC_Stmt::Control_Flow_IC_Stmt(Tgt_Op op, Ics_Opd * opd1, Ics_Opd * opd2, string name) {
	offset = 0 ;
	label_name = name;
	CHECK_INVARIANT((machine_dscr_object.spim_instruction_table[op] != NULL),
			"Instruction description in spim table cannot be null");

	op_desc = *(machine_dscr_object.spim_instruction_table[op]);
	l_opd = opd1;
	r_opd = opd2;
}
	
	
Control_Flow_IC_Stmt::~Control_Flow_IC_Stmt(){}

Instruction_Descriptor & Control_Flow_IC_Stmt::get_inst_op_of_ics(){}

void Control_Flow_IC_Stmt::print_icode(ostream & file_buffer) {
	Icode_Format ic_format = op_desc.get_ic_format();
	string op_name = op_desc.get_name();
	switch (ic_format)
	{
	case i_op: 
		file_buffer << "\t" <<  op_name << "\n";
		break; 
	case i_op_o1: 
		file_buffer << "\t" <<  op_name << " " << label_name ;
		file_buffer << "\n";
		break; 
	case i_branch:
		file_buffer << "\t" << op_name ;
		if (op_name.size()<7) 
			file_buffer << ":\t\t";
		else if (op_name.size()<15)
			file_buffer << ":\t";
		else
			file_buffer << ":";
		l_opd->print_ics_opd(file_buffer);
		file_buffer << " , ";
		r_opd->print_ics_opd(file_buffer);
		file_buffer << " : goto " << label_name;
		file_buffer << "\n";
		break;

	default: CHECK_INVARIANT(CONTROL_SHOULD_NOT_REACH, "Intermediate code format not supported");
		break;
	}
}

void Control_Flow_IC_Stmt::print_assembly(ostream & file_buffer) {
	string op_name = op_desc.get_mnemonic();
	
	Assembly_Format assem_format = op_desc.get_assembly_format();
	switch (assem_format)
	{
	case a_op_r: 
		file_buffer << "\t" << op_name << " " << label_name ; 
		if (curr_procedure) file_buffer << "_" << curr_procedure->get_proc_name() ;
		file_buffer << endl;
		break; 
	case a_op_o1: 
		if (offset != 0 )
			file_buffer << "\tsub $sp, $sp, " << offset << endl;
		file_buffer << "\t" << op_name << " " << label_name << endl;
		if (offset != 0 )
			file_buffer << "\tadd $sp, $sp, " << offset << endl;
		break; 
	case a_branch:
		file_buffer << "\t" << op_name << " ";
		l_opd->print_asm_opd(file_buffer);
		file_buffer << ", ";
		r_opd->print_asm_opd(file_buffer);
		file_buffer << ", " << label_name << endl;
		break;

	default: CHECK_INVARIANT(CONTROL_SHOULD_NOT_REACH, "Intermediate code format not supported");
		break;
	}
}
/******************************Class Compute_IC_Stmt ***************************/
Compute_IC_Stmt::Compute_IC_Stmt() 
{}

Compute_IC_Stmt::Compute_IC_Stmt(Tgt_Op op, Ics_Opd * res, Ics_Opd * lhs, Ics_Opd * rhs) {
	CHECK_INVARIANT((machine_dscr_object.spim_instruction_table[op] != NULL),
			"Instruction description in spim table cannot be null");
	
	op_desc = *(machine_dscr_object.spim_instruction_table[op]);
	result = res;
	l_opd = lhs;
	r_opd = rhs;
}
Compute_IC_Stmt::~Compute_IC_Stmt() 
{}

Instruction_Descriptor & Compute_IC_Stmt::get_inst_op_of_ics() {}

void Compute_IC_Stmt::print_icode(ostream & file_buffer) {
  CHECK_INVARIANT (l_opd, "Left Opd cannot be NULL for a Compute IC Stmt");
	CHECK_INVARIANT (r_opd, "Right Opd cannot be NULL for a Compute IC Stmt");
	CHECK_INVARIANT (result, "Result cannot be NULL for a Compute IC Stmt");

	string operation_name = op_desc.get_name();

	Icode_Format ic_format = op_desc.get_ic_format();

	switch (ic_format)
	{
	case i_r_o1_op_o2: 
			file_buffer << "\t" << operation_name ;
			if (operation_name.size()<7) 
				file_buffer << ":\t\t";
			else if (operation_name.size()<15)
				file_buffer << ":\t";
			else
				file_buffer << ":";
			result->print_ics_opd(file_buffer);
			file_buffer << " <- ";
			l_opd->print_ics_opd(file_buffer);
			file_buffer << " , " ;
			r_opd->print_ics_opd(file_buffer);
			file_buffer << "\n";
			break; 

	default: CHECK_INVARIANT(CONTROL_SHOULD_NOT_REACH, 
				"Intermediate code format not supported");
		break;
	}
}
void Compute_IC_Stmt::print_assembly(ostream & file_buffer) {
	CHECK_INVARIANT (l_opd, "Left Opd cannot be NULL for a Compute IC Stmt");
	CHECK_INVARIANT (r_opd, "Right Opd cannot be NULL for a Compute IC Stmt");
	CHECK_INVARIANT (result, "Result cannot be NULL for a Compute IC Stmt");

	string operation_name = op_desc.get_mnemonic();

	Assembly_Format asm_format = op_desc.get_assembly_format();

	switch (asm_format)
	{
	case a_op_r_o1_o2: 
			file_buffer << "\t" << operation_name << " ";
			result->print_asm_opd(file_buffer);
			file_buffer << ", ";
			l_opd->print_asm_opd(file_buffer);
			file_buffer << ", " ;
			r_opd->print_asm_opd(file_buffer);
			file_buffer << "\n";
			break; 

	default: CHECK_INVARIANT(CONTROL_SHOULD_NOT_REACH, 
				"Intermediate code format not supported");
		break;
	}
}


/******************************Class Unary_IC_Stmt ***************************/
Unary_IC_Stmt::Unary_IC_Stmt() 
{}

Unary_IC_Stmt::Unary_IC_Stmt(Tgt_Op op, Ics_Opd * res,  Ics_Opd * rhs) {
	CHECK_INVARIANT((machine_dscr_object.spim_instruction_table[op] != NULL),
			"Instruction description in spim table cannot be null");
	
	op_desc = *(machine_dscr_object.spim_instruction_table[op]);
	result = res;
	opd = rhs;
}
Unary_IC_Stmt::~Unary_IC_Stmt() 
{}

Instruction_Descriptor & Unary_IC_Stmt::get_inst_op_of_ics() {}

void Unary_IC_Stmt::print_icode(ostream & file_buffer) {
	CHECK_INVARIANT (opd, "Right Opd cannot be NULL for a Compute IC Stmt");
	CHECK_INVARIANT (result, "Result cannot be NULL for a Compute IC Stmt");

	string operation_name = op_desc.get_name();

	Icode_Format ic_format = op_desc.get_ic_format();

	switch (ic_format)
	{
	case i_r_op_o1: 
			file_buffer << "\t" << operation_name ;
			if (operation_name.size()<7) 
				file_buffer << ":\t\t";
			else if (operation_name.size()<15)
				file_buffer << ":\t";
			else
				file_buffer << ":";
			result->print_ics_opd(file_buffer);
			file_buffer << " <- ";
			opd->print_ics_opd(file_buffer);
			file_buffer << "\n";
			break; 

	default: CHECK_INVARIANT(CONTROL_SHOULD_NOT_REACH, 
				"Intermediate code format not supported");
		break;
	}
}
void Unary_IC_Stmt::print_assembly(ostream & file_buffer) {
	CHECK_INVARIANT (opd, "Right Opd cannot be NULL for a IC Stmt");
	CHECK_INVARIANT (result, "Result cannot be NULL for a IC Stmt");

	string operation_name = op_desc.get_mnemonic();

	Assembly_Format asm_format = op_desc.get_assembly_format();

	switch (asm_format)
	{
	case a_op_r_o1: 
			file_buffer << "\t" << operation_name << " ";
			result->print_asm_opd(file_buffer);
			file_buffer << ", ";
			opd->print_asm_opd(file_buffer);
			file_buffer << "\n";
			break; 

	default: CHECK_INVARIANT(CONTROL_SHOULD_NOT_REACH, 
				"Intermediate code format not supported");
		break;
	}
}

/******************************Class Store_Param_IC_Stmt ***************************/
Store_Param_IC_Stmt::Store_Param_IC_Stmt() 
{}

Store_Param_IC_Stmt::Store_Param_IC_Stmt(Tgt_Op op, Ics_Opd * res, Ics_Opd * val, int off) {
	CHECK_INVARIANT((machine_dscr_object.spim_instruction_table[op] != NULL),
			"Instruction description in spim table cannot be null");
	
	op_desc = *(machine_dscr_object.spim_instruction_table[op]);
	result = res;
	opd = val;
	offset = off ;
}
Store_Param_IC_Stmt::~Store_Param_IC_Stmt() 
{}

Instruction_Descriptor & Store_Param_IC_Stmt::get_inst_op_of_ics() {}

void Store_Param_IC_Stmt::print_icode(ostream & file_buffer) {
	CHECK_INVARIANT (opd, "Opd1 cannot be NULL for a store IC Stmt");
	CHECK_INVARIANT (result, "Result cannot be NULL for a store IC Stmt");

	string operation_name = op_desc.get_name();

	Icode_Format ic_format = op_desc.get_ic_format();

	switch (ic_format)
	{
	case i_r_op_o1: 
			file_buffer << "\t" << operation_name ;
			if (operation_name.size()<7) 
				file_buffer << ":\t\t";
			else if (operation_name.size()<15)
				file_buffer << ":\t";
			else
				file_buffer << ":";
			result->print_ics_opd(file_buffer);
			file_buffer << " <- ";
			opd->print_ics_opd(file_buffer);
			file_buffer << "\n";

			break; 

	default: CHECK_INVARIANT(CONTROL_SHOULD_NOT_REACH, 
				"Intermediate code format not supported");
		break;
	}
}
void Store_Param_IC_Stmt::print_assembly(ostream & file_buffer) {
	CHECK_INVARIANT (opd, "Opd cannot be NULL for a store IC Stmt");
	CHECK_INVARIANT (result, "Result cannot be NULL for a store IC Stmt");
	string op_name = op_desc.get_mnemonic();

	Assembly_Format assem_format = op_desc.get_assembly_format();
	switch (assem_format)
	{
	case a_op_o1_r: 
	  	file_buffer << "\t" << op_name << " ";
		opd->print_asm_opd(file_buffer);
		file_buffer << ", ";
		file_buffer << -offset << "($sp)";
		file_buffer << "\n";

		break; 

	default: 
		CHECK_INVARIANT(CONTROL_SHOULD_NOT_REACH, 
				"Intermediate code format not supported");
		break;
	}
}


/******************************* Class Code_For_Ast ****************************/

Code_For_Ast::Code_For_Ast()
{
	ics_list = *new list<Icode_Stmt *>;
}

Code_For_Ast::Code_For_Ast(list<Icode_Stmt *> & ic_l, Register_Descriptor * reg)
{
	ics_list = ic_l;
	result_register = reg;
}

void Code_For_Ast::append_ics(Icode_Stmt & ic_stmt)
{
	ics_list.push_back(&ic_stmt);
	Ics_Opd * result = ic_stmt.get_result();
	result_register = result->get_reg();
}

list<Icode_Stmt *> & Code_For_Ast::get_icode_list()  
{ 
	return ics_list; 
}

Register_Descriptor * Code_For_Ast::get_reg()
{
	return result_register;
}

Code_For_Ast& Code_For_Ast::operator=(const Code_For_Ast& rhs)
{
	ics_list = rhs.ics_list;
	result_register = rhs.result_register;

	return *this;
}

/************************ class Instruction_Descriptor ********************************/

Tgt_Op Instruction_Descriptor::get_op()                   	{ return inst_op; }
string Instruction_Descriptor::get_name()                       { return name; }
string Instruction_Descriptor::get_mnemonic()                   { return mnemonic; }
string Instruction_Descriptor::get_ic_symbol()                  { return ic_symbol; }
Icode_Format Instruction_Descriptor::get_ic_format()            { return ic_format; }
Assembly_Format Instruction_Descriptor::get_assembly_format()   { return assem_format; }

Instruction_Descriptor::Instruction_Descriptor (Tgt_Op op, string temp_name, string temp_mnemonic, 
						string ic_sym, Icode_Format ic_form, Assembly_Format as_form)
{
	inst_op = op;
	name = temp_name; 
	mnemonic = temp_mnemonic;
	ic_symbol = ic_sym;
	ic_format = ic_form;
	assem_format = as_form;
}

Instruction_Descriptor::Instruction_Descriptor()
{
	inst_op = nop;
	name = "";
	mnemonic = "";
	ic_symbol = "";
	ic_format = i_nsy;
	assem_format = a_nsy;
}

template class Const_Opd<int>;
template class Const_Opd<float>;
