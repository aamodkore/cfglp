
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

#ifndef AST_HH
#define AST_HH

#include<string>
#include<iostream>
#include<iomanip>
#include<typeinfo>
#include<list>

#define AST_SPACE "         "
#define AST_NODE_SPACE "            "
#define AST_SUB_NODE_SPACE "               "

using namespace std;
class Procedure;
class Ast;

extern Procedure * curr_procedure;

enum Relational_Operator { 
	greater_than_op, greater_equals_op, 
	less_than_op, less_equals_op, 
	equals_op, not_equals_op 
};

class Ast
{
protected:
	typedef enum
	{
		zero_arity = 0,
		unary_arity = 1,
		binary_arity = 2
	}Ast_Arity;

	Data_Type node_data_type;
	Ast_Arity ast_num_child;

	int lineno;

public:
	Ast();
	~Ast();

	void set_data_type(Data_Type dt) ;
	virtual Data_Type get_data_type();
	virtual bool check_ast();
	virtual Symbol_Table_Entry & get_symbol_entry();

	virtual void print(ostream & file_buffer) = 0;
	virtual void print_value(Local_Environment & eval_env, ostream & file_buffer);

	virtual Eval_Result & get_value_of_evaluation(Local_Environment & eval_env);
	virtual void set_value_of_evaluation(Local_Environment & eval_env, Eval_Result & result);
	virtual Eval_Result & evaluate(Local_Environment & eval_env, ostream & file_buffer) = 0;

	virtual Code_For_Ast & compile() = 0;
	virtual Code_For_Ast & compile_and_optimize_ast(Lra_Outcome & lra) = 0;
	virtual Code_For_Ast & create_store_stmt(Register_Descriptor * store_register);
};

class Assignment_Ast:public Ast
{
	Ast * lhs;
	Ast * rhs;

public:
	Assignment_Ast(Ast * temp_lhs, Ast * temp_rhs, int line);
	~Assignment_Ast();

	bool check_ast();

	void print(ostream & file_buffer);

	Eval_Result & evaluate(Local_Environment & eval_env, ostream & file_buffer);

	Code_For_Ast & compile();
	Code_For_Ast & compile_and_optimize_ast(Lra_Outcome & lra);
};

class Name_Ast:public Ast
{
	Symbol_Table_Entry * variable_symbol_entry;

public:
	Name_Ast(string & name, Symbol_Table_Entry & var_entry, int line);
	~Name_Ast();

	Data_Type get_data_type();
	Symbol_Table_Entry & get_symbol_entry();

	void print(ostream & file_buffer);

	void print_value(Local_Environment & eval_env, ostream & file_buffer);
	Eval_Result & get_value_of_evaluation(Local_Environment & eval_env);
	void set_value_of_evaluation(Local_Environment & eval_env, Eval_Result & result);
	Eval_Result & evaluate(Local_Environment & eval_env, ostream & file_buffer);

	Code_For_Ast & compile();
	Code_For_Ast & compile_and_optimize_ast(Lra_Outcome & lra);
	Code_For_Ast & create_store_stmt(Register_Descriptor * store_register);
};

template <class T>
class Number_Ast:public Ast
{
	T constant;

public:
	Number_Ast(T number, Data_Type constant_data_type, int line);
	~Number_Ast();

	Data_Type get_data_type();
	
	void print(ostream & file_buffer);
	
	Eval_Result & evaluate(Local_Environment & eval_env, ostream & file_buffer);

	Code_For_Ast & compile();
	Code_For_Ast & compile_and_optimize_ast(Lra_Outcome & lra);
};

class Return_Ast:public Ast
{
	Ast * return_exp;
	
public:
	Return_Ast(int line);
	Return_Ast(Ast *, int line);
	~Return_Ast();

	void print(ostream & file_buffer);

	Eval_Result & evaluate(Local_Environment & eval_env, ostream & file_buffer);

	Code_For_Ast & compile();
	Code_For_Ast & compile_and_optimize_ast(Lra_Outcome & lra);
};

class Goto_Ast:public Ast 
{

public:
	Goto_Ast();
	~Goto_Ast();

	virtual bool check_ast() ;
	virtual void print(ostream & file_buffer) = 0 ;
	virtual Eval_Result & evaluate(Local_Environment & eval_env, ostream & file_buffer) = 0;
  
	virtual Code_For_Ast & compile() = 0 ;
	virtual Code_For_Ast & compile_and_optimize_ast(Lra_Outcome & lra) = 0 ;
};


class Unconditional_Goto_Ast: public Goto_Ast 
{
 	int block_no;

public:
	Unconditional_Goto_Ast();
	Unconditional_Goto_Ast(int bb);
	~Unconditional_Goto_Ast();

	void print(ostream & file_buffer);
	Eval_Result & evaluate(Local_Environment & eval_env, ostream & file_buffer);

	Code_For_Ast & compile();
	Code_For_Ast & compile_and_optimize_ast(Lra_Outcome & lra);
};

class Conditional_Goto_Ast: public Goto_Ast 
{
 	Ast * condition ;
 	int if_goto;
 	int else_goto ;

public:
	Conditional_Goto_Ast();
	Conditional_Goto_Ast(Ast* cond, int if_g, int else_g);
	~Conditional_Goto_Ast();

	bool check_ast() ;
	void print(ostream & file_buffer);
	Eval_Result & evaluate(Local_Environment & eval_env, ostream & file_buffer);

	Code_For_Ast & compile();
	Code_For_Ast & compile_and_optimize_ast(Lra_Outcome & lra);
};



class Relational_Expr_Ast:public Ast
{
	Ast * lhs;
	Ast * rhs;
	Relational_Operator relational_op ;

public:
	Relational_Expr_Ast(Ast* temp_lhs, Relational_Operator op, Ast* temp_rhs) ;
	~Relational_Expr_Ast() ;

	Data_Type get_data_type();
	bool check_ast();
	void print(ostream & file_buffer);
	
	Eval_Result & evaluate(Local_Environment & eval_env, ostream & file_buffer);

	Code_For_Ast & compile();
	Code_For_Ast & compile_and_optimize_ast(Lra_Outcome & lra);
};


class Arithmetic_Expr_Ast:public Ast
{
protected:
	Ast * lhs;
	Ast * rhs;
public:
	Arithmetic_Expr_Ast() ;
	~Arithmetic_Expr_Ast() ;

	virtual Data_Type get_data_type();
	bool check_ast();
	virtual void print(ostream & file_buffer) = 0;
	
	virtual Eval_Result & evaluate(Local_Environment & eval_env, ostream & file_buffer) = 0;

	virtual Code_For_Ast & compile();
	virtual Code_For_Ast & compile_and_optimize_ast(Lra_Outcome & lra);
};


class Plus_Ast:public Arithmetic_Expr_Ast
{
public:
	Plus_Ast(Ast * l, Ast * r) ;
	~Plus_Ast() ;

	Data_Type get_data_type();
 
	void print(ostream & file_buffer);
	
	Eval_Result & evaluate(Local_Environment & eval_env, ostream & file_buffer);

	Code_For_Ast & compile();
	Code_For_Ast & compile_and_optimize_ast(Lra_Outcome & lra);
};

class Minus_Ast:public Arithmetic_Expr_Ast
{

public:
	Minus_Ast(Ast * l, Ast * r) ;
	~Minus_Ast() ;

	Data_Type get_data_type();
	
	void print(ostream & file_buffer);
	Eval_Result & evaluate(Local_Environment & eval_env, ostream & file_buffer);

	Code_For_Ast & compile();
	Code_For_Ast & compile_and_optimize_ast(Lra_Outcome & lra);

};

class Multiplication_Ast:public Arithmetic_Expr_Ast
{
public:
	Multiplication_Ast(Ast * l, Ast * r) ;
	~Multiplication_Ast() ;

	Data_Type get_data_type();
	void print(ostream & file_buffer);
	
    Eval_Result & evaluate(Local_Environment & eval_env, ostream & file_buffer);

    Code_For_Ast & compile();
	Code_For_Ast & compile_and_optimize_ast(Lra_Outcome & lra);
};

class Division_Ast:public Arithmetic_Expr_Ast
{

public:
	Division_Ast(Ast * l, Ast * r) ;
	~Division_Ast() ;

	Data_Type get_data_type();
  
	void print(ostream & file_buffer);
	
	Eval_Result & evaluate(Local_Environment & eval_env, ostream & file_buffer);

	Code_For_Ast & compile();
	Code_For_Ast & compile_and_optimize_ast(Lra_Outcome & lra);
};

class Unary_Ast:public Arithmetic_Expr_Ast
{
public:
	Unary_Ast(Ast * r) ;
	~Unary_Ast() ;

        Data_Type get_data_type();
	
	void print(ostream & file_buffer);
  
        bool check_ast();
	Eval_Result & evaluate(Local_Environment & eval_env, ostream & file_buffer);

	Code_For_Ast & compile();
	Code_For_Ast & compile_and_optimize_ast(Lra_Outcome & lra);
};


class Type_Cast_Ast:public Arithmetic_Expr_Ast
{
public:
	Type_Cast_Ast(Ast * r, Data_Type dt) ;
	~Type_Cast_Ast() ;

   Data_Type get_data_type();
	
	void print(ostream & file_buffer);
  
    bool check_ast();
	Eval_Result & evaluate(Local_Environment & eval_env, ostream & file_buffer);

	Code_For_Ast & compile();
	Code_For_Ast & compile_and_optimize_ast(Lra_Outcome & lra);
};



class Call_Ast:public Ast
{
	Procedure * fn;
	list<Ast *> arguments;

public:
	Call_Ast();
	Call_Ast(Procedure * f);
	Call_Ast(Procedure * f, list<Ast *> args);
	~Call_Ast();

	void print(ostream & file_buffer);
	Data_Type get_data_type();
	bool check_ast();
	Eval_Result & evaluate(Local_Environment & eval_env, ostream & file_buffer);

	Code_For_Ast & compile();
	Code_For_Ast & compile_and_optimize_ast(Lra_Outcome & lra);
};


#endif
