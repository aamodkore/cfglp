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

#ifndef AST2_HH
#define AST2_HH

#include <string>
#include "ast.hh"
#define AST_SPACE "         "
#define AST_NODE_SPACE "            "

using namespace std; 



class Relational_Expr_Ast:public Ast
{

public:
	Relational_Expr_Ast() ;
	~Relational_Expr_Ast() ;

	Data_Type get_data_type();
	
	void print_ast(ostream & file_buffer);
	void print_value(Local_Environment & eval_env, ostream & file_buffer);

	Eval_Result & get_value_of_evaluation(Local_Environment & eval_env);
	void set_value_of_evaluation(Local_Environment & eval_env, Eval_Result & result);
	Eval_Result & evaluate(Local_Environment & eval_env, ostream & file_buffer);
};

#endif
