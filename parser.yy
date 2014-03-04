
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

%scanner ../scanner.h
%scanner-token-function d_scanner.lex()
%filenames parser
%parsefun-source parser.cc

%union 
{
	int integer_value;
	float float_value;
	std::string * string_value;
	list<Ast *> * ast_list;
	Ast * ast;
	Symbol_Table * symbol_table;
	Symbol_Table_Entry * symbol_entry;
	Basic_Block * basic_block;
	list<Basic_Block *> * basic_block_list;
	Procedure * procedure;
	enum Relational_Operator rel_op;
};

%token <integer_value> INTEGER_NUMBER
%token <integer_value> BB
%token <float_value> FLOAT_NUMBER
%token <string_value> NAME
%token RETURN INTEGER FLOAT DOUBLE VOID IF ELSE GOTO
%token ASSIGN_OP NE EQ LT LE GT GE

%type <symbol_table> declaration_statement_list
%type <symbol_table> arguement_list
%type <symbol_entry> declaration_statement
%type <symbol_entry> arguement
%type <basic_block_list> basic_block_list
%type <basic_block> basic_block
%type <ast_list> executable_statement_list
%type <ast_list> assignment_statement_list
%type <ast_list> expression_list
%type <ast> assignment_statement
%type <ast> if_else_statement
%type <ast> goto_statement

%type <ast> expression
%type <ast> identifier
%type <ast> primary_expression
%type <ast> unary_expression
%type <ast> multiplicative_expression
%type <ast> additive_expression
%type <ast> arithmetic_expression
%type <ast> comparison_expression
%type <ast> equality_expression

%type <rel_op> comparison_operator
%type <rel_op> equality_operator
%type <ast> variable
%type <ast> constant

%start program

%%

program:
	procedure_list
|
	declaration_statement_list procedure_list
;

procedure_list :
	procedure_declaration_list procedure_definition_list
|
	procedure_definition_list
;

procedure_declaration :
	VOID procedure_name ';'
|
	INTEGER procedure_name ';'
|
	FLOAT procedure_name ';'
;


procedure_declaration_list:
	procedure_declaration_list procedure_declaration
|
	procedure_declaration
;


procedure_definition :
	procedure_name procedure_body
;

procedure_definition_list:
	procedure_definition_list procedure_definition
|
	procedure_definition
;


arguement_list:
	arguement_list ',' arguement
	{
		// if declaration is local then no need to check in global list
		// if declaration is global then this list is global list

		int line = get_line_number();
		string var_name = $3->get_variable_name();
		program_object.variable_in_proc_map_check($3->get_variable_name(), line);

		if ($1 != NULL)
		{
			if($1->variable_in_symbol_list_check(var_name))
			{
				int line = get_line_number();
				report_error("Variable is declared twice", line);
			}

			$$ = $1;
		}

		else
			$$ = new Symbol_Table();

		$$->push_symbol($3);
	}
|
	arguement
	{
		int line = get_line_number();
		program_object.variable_in_proc_map_check($1->get_variable_name(), line);

		$$ = new Symbol_Table();
		$$->push_symbol($1);	
	}
;


arguement:
	INTEGER NAME
	{
		$$ = new Symbol_Table_Entry(*$2, int_data_type);
		delete $2;
	}
|
	FLOAT NAME
	{
		$$ = new Symbol_Table_Entry(*$2, int_data_type);
		delete $2;
	}
;


procedure_name:
	NAME '(' ')'
	{
		current_procedure = new Procedure(void_data_type, *$1);
	}
|
	NAME '(' arguement_list ')'
	{
		current_procedure = new Procedure(void_data_type, *$1);
		current_procedure->set_argument_list(*$3);
	}
;

procedure_body:
	'{' declaration_statement_list
	{
		current_procedure->set_local_list(*$2);
		delete $2;
	}
	basic_block_list '}'
	{
		if (return_statement_used_flag == false)
		{
			int line = get_line_number();
			report_error("Atleast 1 basic block should have a return statement", line);
		}

		current_procedure->set_basic_block_list(*$4);

		delete $4;
	}
|
	'{' basic_block_list '}'
	{
		/*
		if (return_statement_used_flag == false)
		{
			int line = get_line_number();
			report_error("Atleast 1 basic block should have a return statement", line);
		}
		*/
		current_procedure->set_basic_block_list(*$2);

		delete $2;
	}
;

declaration_statement_list:
	declaration_statement
	{
		int line = get_line_number();
		program_object.variable_in_proc_map_check($1->get_variable_name(), line);

		string var_name = $1->get_variable_name();
		if (current_procedure && current_procedure->get_proc_name() == var_name)
		{
			int line = get_line_number();
			report_error("Variable name cannot be same as procedure name", line);
		}

		$$ = new Symbol_Table();
		$$->push_symbol($1);
	}
|
	declaration_statement_list declaration_statement
	{
		// if declaration is local then no need to check in global list
		// if declaration is global then this list is global list

		int line = get_line_number();
		program_object.variable_in_proc_map_check($2->get_variable_name(), line);

		string var_name = $2->get_variable_name();
		if (current_procedure && current_procedure->get_proc_name() == var_name)
		{
			int line = get_line_number();
			report_error("Variable name cannot be same as procedure name", line);
		}

		if ($1 != NULL)
		{
			if($1->variable_in_symbol_list_check(var_name))
			{
				int line = get_line_number();
				report_error("Variable is declared twice", line);
			}

			$$ = $1;
		}

		else
			$$ = new Symbol_Table();

		$$->push_symbol($2);
	}
;

declaration_statement:
	INTEGER NAME ';'
	{
		$$ = new Symbol_Table_Entry(*$2, int_data_type);
		delete $2;
	}
|
	FLOAT NAME ';'
	{
		$$ = new Symbol_Table_Entry(*$2, float_data_type);
		delete $2;
	}
;

basic_block_list:
	basic_block_list basic_block
	{
		if (!$2)
		{
			int line = get_line_number();
			report_error("Basic block doesn't exist", line);
		}

		bb_strictly_increasing_order_check($$, $2->get_bb_number());

		$$ = $1;
		$$->push_back($2);
	}
|
	basic_block
	{
		if (!$1)
		{
			int line = get_line_number();
			report_error("Basic block doesn't exist", line);
		}

		$$ = new list<Basic_Block *>;
		$$->push_back($1);
	}
	
;

basic_block:
	BB ':' executable_statement_list
	{
	       $$ = new Basic_Block($1, *$3);	
	}
;

executable_statement_list:
	assignment_statement_list
	{
		$$ = $1;
	}
|
	assignment_statement_list return_statement
	{
		Ast * ret = new Return_Ast();

		return_statement_used_flag = true;					// Current procedure has an occurrence of return statement

		if ($1 != NULL)
			$$ = $1;

		else
			$$ = new list<Ast *>;

		$$->push_back(ret);
	}
|
	assignment_statement_list 
	goto_statement
	{
		if ($1 != NULL)
			$$ = $1;

		else
			$$ = new list<Ast *>;

		$$->push_back($2);
	}		

|
	assignment_statement_list
	if_else_statement 
	{
		if ($1 != NULL)
			$$ = $1;
		else
			$$ = new list<Ast *>;

		$$->push_back($2);
	}
;


assignment_statement_list:
	{
		$$ = NULL;
	}
|
	assignment_statement_list assignment_statement
	{
		if ($1 == NULL)
			$$ = new list<Ast *>;

		else
			$$ = $1;

		$$->push_back($2);
	}
|
	assignment_statement_list function_call ';'
	{
		if ($1 == NULL)
			$$ = new list<Ast *>;

		else
			$$ = $1;
	}
;

assignment_statement:
	variable ASSIGN_OP expression ';' 
	{
		$$ = new Assignment_Ast($1, $3);
		int line = get_line_number();
		// $$->check_ast(line);
	}
;

if_else_statement: 
        IF '(' expression ')' 
        GOTO BB ';'
        ELSE 
        GOTO BB ';'
	{
		$$ = new Conditional_Goto_Ast($3, $6, $10);
	}
;

goto_statement : 
        GOTO BB ';'
	{
		$$ = new Unconditional_Goto_Ast($2);
	}
		
;

return_statement :
	RETURN ';'
|
	RETURN expression ';'
;	

identifier :
	variable   	
	{ $$ = $1; }
|
	constant	
	{ $$ = $1; }
;

primary_expression:
	identifier	
	{
		$$ = $1; 
	}
|	
	'(' expression ')'
	{ 
		$$ = $2; 
	}
;

unary_expression:
	'-' unary_expression 
	{ 
		$$ = new Unary_Ast($2);
		int line = get_line_number();
		// $$->check_ast(line);
	} 
|
	'(' FLOAT ')' unary_expression 
	{
		$$ = $4;
		$$->set_data_type(float_data_type);
	}
|
	'(' INTEGER ')' unary_expression 
	{
		$4->set_data_type(int_data_type);
		$$ = $4;
	}
|
	'(' DOUBLE ')' unary_expression 
	{
		$$ = $4;
		$$->set_data_type(float_data_type);
	}
|
	primary_expression 
	{
		$$ = $1; 
	} 
|
	function_call 
	{
		Ast * ret = new Return_Ast();
		$$ = ret ;
	}
;


function_call:
	NAME '(' expression_list ')'
|
	NAME '(' ')'
;

multiplicative_expression:
	multiplicative_expression '*' unary_expression
	{
		$$ = new Multiplication_Ast($1, $3);
		int line = get_line_number();
		// $$->check_ast(line);
	}
|
	multiplicative_expression '/' unary_expression
	{
		$$ = new Division_Ast($1, $3);
		int line = get_line_number();
		// $$->check_ast(line);
	}
|
	unary_expression
	{
		$$ = $1;
	}
;

additive_expression:
	additive_expression '+'  multiplicative_expression
	{
		$$ = new Plus_Ast($1, $3);
		int line = get_line_number();
		// $$->check_ast(line);
	}
|
	additive_expression '-'  multiplicative_expression
	{
		$$ = new Minus_Ast($1, $3);
		int line = get_line_number();
		// $$->check_ast(line);
	}
|	
	multiplicative_expression { $$ = $1; }
;

arithmetic_expression : additive_expression 
	{ $$ = $1; }
;

comparison_expression :
        comparison_expression comparison_operator arithmetic_expression
	{
		$$ = new Relational_Expr_Ast($1, $2, $3);
		int line = get_line_number(); 
		// $$->check_ast(line);
	} 
|
	arithmetic_expression
			{ $$ = $1 ;}
;

equality_expression :
        equality_expression equality_operator comparison_expression
	{
		$$ = new Relational_Expr_Ast($1, $2, $3);
		int line = get_line_number(); 
		// $$->check_ast(line);
	} 
|
	comparison_expression
			{ $$ = $1 ;}
;

expression: equality_expression { $$ = $1; }
;

expression_list :
	expression_list ',' expression
	{
		$$ = $1 ;
		$$->push_back($3);
	}
|
	expression
	{
		$$ = new list<Ast *>;
		$$->push_back($1);
	}
;

comparison_operator :
    GE    { $$ = greater_equals_op; } 
| 
	LE    { $$ = less_equals_op; }
| 
	GT    { $$ = greater_than_op; }
| 
	LT    { $$ = less_than_op; } 
;

equality_operator : 
	EQ    { $$ = equals_op; }	
| 
	NE    { $$ = not_equals_op; }	 
;

variable:
	NAME
	{
		Symbol_Table_Entry var_table_entry;

		if (current_procedure->variable_in_symbol_list_check(*$1))
			 var_table_entry = current_procedure->get_symbol_table_entry(*$1);

		else if (program_object.variable_in_symbol_list_check(*$1))
			var_table_entry = program_object.get_symbol_table_entry(*$1);

		else
		{
			// int line = get_line_number();
			// report_error("Variable has not been declared", line);
		}

		$$ = new Name_Ast(*$1, var_table_entry);

		delete $1;
	}
;

constant:
	INTEGER_NUMBER
	{
		$$ = new Number_Ast<int>($1, int_data_type);
	}
|
	FLOAT_NUMBER
	{
		$$ = new Number_Ast<float>($1, float_data_type);
	}
;
