
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

#ifndef LOCAL_ENVIRONMENT_HH
#define LOCAL_ENVIRONMENT_HH

#include<iomanip>
#include<string>
#include<map>

#define VAR_SPACE "         "

using namespace std;

typedef enum
{
	int_result,
	float_result,
	void_result,
	bool_result,
	bb_result,
	return_result
} Result_Enum;

class Eval_Result;
class Local_Environment;

class Eval_Result 
{
protected:
	Result_Enum result_type;

public:
	virtual int get_int_value();
	virtual float get_value_float();    
	virtual void set_value(int value);
        virtual void set_value_float(float value);
  // virtual Eval_Result * get_return_result();

	virtual bool is_variable_defined();
	virtual void set_variable_status(bool def);

	virtual void set_result_enum(Result_Enum res) = 0;
	virtual Result_Enum get_result_enum() = 0;
};

class Eval_Result_Value:public Eval_Result
{
public:
	virtual void set_value(int number);
  virtual void set_value_float(float value);
  
	virtual int get_int_value() ;
  virtual float get_value_float() ;
	virtual bool is_variable_defined() = 0;
	virtual void set_variable_status(bool def) = 0;

	virtual void set_result_enum(Result_Enum res) = 0;
	virtual Result_Enum get_result_enum() = 0;
};

class Eval_Result_Value_Int:public Eval_Result_Value
{
	int value;
	bool defined;
public:
	Eval_Result_Value_Int();
  Eval_Result_Value_Int(int n);
  ~Eval_Result_Value_Int();

	void set_value(int number);
	int get_int_value();

	void set_variable_status(bool def);
	bool is_variable_defined();

	void set_result_enum(Result_Enum res);
	Result_Enum get_result_enum();
};

class Eval_Result_Value_Float:public Eval_Result_Value
{
	float value;
	bool defined;
public:
	Eval_Result_Value_Float();
  Eval_Result_Value_Float(float n);
	~Eval_Result_Value_Float();

	void set_value_float(float number);
  float get_value_float();

	void set_variable_status(bool def);
	bool is_variable_defined();

	void set_result_enum(Result_Enum res);
	Result_Enum get_result_enum();
};



class Eval_Result_Value_Bool:public Eval_Result_Value
{
	bool value;
	bool defined;
public:
	Eval_Result_Value_Bool();
	~Eval_Result_Value_Bool();

	void set_value(int number);
	int get_int_value();

	void set_variable_status(bool def);
	bool is_variable_defined();

	void set_result_enum(Result_Enum res);
	Result_Enum get_result_enum();
};

/*
class Eval_Result_Value_Return:public Eval_Result
{
	Eval_Result * return_value;
	bool defined;

public:
	Eval_Result_Value_Return();
	Eval_Result_Value_Return(Eval_Result * retval);
	~Eval_Result_Value_Return();

	Eval_Result * get_return_result();
       	
	void set_result_enum(Result_Enum res);
	Result_Enum get_result_enum();
};
*/


class Eval_Result_BB:public Eval_Result
{
	int block_no;
	bool valid;
public:
  Eval_Result_BB();
  Eval_Result_BB(int n);  
  ~Eval_Result_BB();
  
  void set_value(int number);
  int get_int_value();
  
  void set_variable_status(bool def);
  bool is_variable_defined();
  
  void set_result_enum(Result_Enum res);
  Result_Enum get_result_enum();
};

class Local_Environment
{
	map<string, Eval_Result *> variable_table;

public:
	Local_Environment();
	~Local_Environment();

	void print(ostream & file_buffer);
	bool is_variable_defined(string name);
	Eval_Result * get_variable_value(string name);
	void put_variable_value(Eval_Result & value, string name);
	bool does_variable_exist(string name);
};


extern Local_Environment interpreter_global_table;

#endif
