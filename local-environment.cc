
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
#include<typeinfo>

using namespace std;

#include"common-classes.hh"
#include"local-environment.hh"
#include"error-display.hh"
#include"user-options.hh"

int Eval_Result::get_int_value()
{
	stringstream msg;
	msg << "No get_value() function for " << typeid(*this).name();
	CHECK_INVARIANT(CONTROL_SHOULD_NOT_REACH, msg.str());
}

float Eval_Result::get_value_float()
{
	stringstream msg;
	msg << "No get_value_float() function for " << typeid(*this).name();
	CHECK_INVARIANT(CONTROL_SHOULD_NOT_REACH, msg.str());
}

void Eval_Result::set_value(int number)
{
	stringstream msg;
	msg << "The set_value(int) function for " << typeid(*this).name();
	CHECK_INVARIANT(CONTROL_SHOULD_NOT_REACH, msg.str());
}

void Eval_Result::set_value_float(float number)
{
	stringstream msg;
	msg << "The set_value(float) function for " << typeid(*this).name();
	CHECK_INVARIANT(CONTROL_SHOULD_NOT_REACH, msg.str());
}


bool Eval_Result::is_variable_defined()
{
	stringstream msg;
	msg << "No is_variable_defined() function for " << typeid(*this).name();
	CHECK_INVARIANT(CONTROL_SHOULD_NOT_REACH, msg.str());
}

void Eval_Result::set_variable_status(bool def)
{
	stringstream msg;
	msg << "No set_variable_status() function for " << typeid(*this).name();
	CHECK_INVARIANT(CONTROL_SHOULD_NOT_REACH, msg.str());
}

///////////////////////////////////////////////////////////////////////////////

void Eval_Result_Value::set_value(int value)
{
	stringstream msg;
	msg << "No set_value() fucntion for " << typeid(*this).name();
	CHECK_INVARIANT(CONTROL_SHOULD_NOT_REACH, msg.str());
}

void Eval_Result_Value::set_value_float(float number)
{
	stringstream msg;
	msg << "The set_value(float) function for " << typeid(*this).name();
	CHECK_INVARIANT(CONTROL_SHOULD_NOT_REACH, msg.str());
}

float Eval_Result_Value::get_value_float()
{
	stringstream msg;
	msg << "No get_value_float() function for " << typeid(*this).name();
	CHECK_INVARIANT(CONTROL_SHOULD_NOT_REACH, msg.str());
}

int Eval_Result_Value::get_int_value()
{
	stringstream msg;
	msg << "No get_value() function for " << typeid(*this).name();
	CHECK_INVARIANT(CONTROL_SHOULD_NOT_REACH, msg.str());
}

///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

Eval_Result_Value_Int::Eval_Result_Value_Int()
{
	value = 0;
	defined = false;
	result_type = int_result;
}

Eval_Result_Value_Int::Eval_Result_Value_Int(int n)
{
	value = n;
	defined = true;
	result_type = int_result;
}

Eval_Result_Value_Int::~Eval_Result_Value_Int()
{ }

void Eval_Result_Value_Int::set_value(int number)
{
	value = number;
	defined = true;
}

int Eval_Result_Value_Int::get_int_value()
{
	return value;
}

void Eval_Result_Value_Int::set_variable_status(bool def)
{
	defined = def;
}

bool Eval_Result_Value_Int::is_variable_defined()
{
	return defined;
}

void Eval_Result_Value_Int::set_result_enum(Result_Enum res)
{
	result_type = res;
}

Result_Enum Eval_Result_Value_Int::get_result_enum()
{
	return result_type;
}
///////////////////////////////////////////////////////////////////////////////

Eval_Result_Value_Float::Eval_Result_Value_Float()
{
	value = 0.0;
	defined = false;
	result_type = float_result;
}

Eval_Result_Value_Float::Eval_Result_Value_Float(float n)
{
	value = n;
	defined = true;
	result_type = float_result;
}

Eval_Result_Value_Float::~Eval_Result_Value_Float()
{ }

void Eval_Result_Value_Float::set_value_float(float number)
{
	value = number;
	defined = true;
}

float Eval_Result_Value_Float::get_value_float()
{
	return value;
}

void Eval_Result_Value_Float::set_variable_status(bool def)
{
	defined = def;
}

bool Eval_Result_Value_Float::is_variable_defined()
{
	return defined;
}

void Eval_Result_Value_Float::set_result_enum(Result_Enum res)
{
	result_type = res;
}

Result_Enum Eval_Result_Value_Float::get_result_enum()
{
	return result_type;
}

///////////////////////////////////////////////////////////////////////////////////

Eval_Result_Value_Bool::Eval_Result_Value_Bool()
{
	value = false;
	defined = false;
	result_type = bool_result;
}

Eval_Result_Value_Bool::~Eval_Result_Value_Bool()
{ }

void Eval_Result_Value_Bool::set_value(int number)
{
	value = (number!=0) ;
	defined = true;
}

int Eval_Result_Value_Bool::get_int_value()
{
	return value?1:0;
}

void Eval_Result_Value_Bool::set_variable_status(bool def)
{
	defined = def;
}

bool Eval_Result_Value_Bool::is_variable_defined()
{
	return defined;
}

void Eval_Result_Value_Bool::set_result_enum(Result_Enum res)
{
	result_type = res;
}

Result_Enum Eval_Result_Value_Bool::get_result_enum()
{
	return result_type;
}
///////////////////////////////////////////////////////////////////////////////////
/*
Eval_Result_Value_Return::Eval_Result_Value_Return()
{
	return_value = NULL;
	defined = false;
	result_type = return_result;
}

Eval_Result_Value_Return::Eval_Result_Value_Return(Eval_Result *retval)
{
	return_value = retval;
	defined = true;
	result_type = return_result;
}

Eval_Result_Value_Return::~Eval_Result_Value_Return()
{ }

Eval_Result * Eval_Result_Value_Return::get_return_result() {
	return return_value;
}

void Eval_Result_Value_Return::set_result_enum(Result_Enum res)
{
	result_type = res;
}

Result_Enum Eval_Result_Value_Return::get_result_enum()
{
	return result_type;
}

*/
///////////////////////////////////////////////////////////////////////////////////

Eval_Result_BB::Eval_Result_BB()
{
	block_no = 0;
	valid = false;
	result_type = bb_result;
}

Eval_Result_BB::Eval_Result_BB(int n)
{
	block_no = n;
	valid = true;
	result_type = bb_result;
}

Eval_Result_BB::~Eval_Result_BB()
{ }

void Eval_Result_BB::set_value(int number)
{
	block_no = number;
}

int Eval_Result_BB::get_int_value()
{
	return block_no;
}

void Eval_Result_BB::set_variable_status(bool def)
{
	valid = def;
}

bool Eval_Result_BB::is_variable_defined()
{
	return valid;
}

void Eval_Result_BB::set_result_enum(Result_Enum res)
{
	result_type = res;
}

Result_Enum Eval_Result_BB::get_result_enum()
{
	return result_type;
}
///////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////
/*
Local_Environment::Local_Environment()
{}

Local_Environment::~Local_Environment()
{}

void Local_Environment::print(ostream & file_buffer)
{
	map<string, Eval_Result_Value *>::iterator i;
	for (i = variable_table.begin(); i != variable_table.end(); i++)
	{
		if (variable_table.find((*i).first) != variable_table.end())
		{
			Eval_Result * vi = variable_table[(*i).first];

			if (vi == NULL)
				continue;

			if (vi->is_variable_defined() == false)
				file_buffer << VAR_SPACE << (*i).first << " : undefined" << "\n";
		
			else
			{
				if (vi->get_result_enum() == int_result)
					file_buffer << VAR_SPACE << (*i).first << " : " << vi->get_int_value() << "\n";
			}
		}
	}
}

bool Local_Environment::is_variable_defined(string name)
{
	if (variable_table.find(name) != variable_table.end())
	{
		Eval_Result * i = variable_table[name];
		return i->is_variable_defined();
	}
	else
		return false;
}

Eval_Result_Value * Local_Environment::get_variable_value(string name)
{
	if (variable_table.find(name) != variable_table.end())
	{
		Eval_Result * i = variable_table[name];
		return (Eval_Result_Value *) i;
	}

	return NULL;
}

void Local_Environment::put_variable_value(Eval_Result_Value & i, string name)
{
	variable_table[name] = &i;
}

bool Local_Environment::does_variable_exist(string name)
{
	if (variable_table.find(name) == variable_table.end())
		return false;
	else
		return true;
}
*/
/////////////////////////////////////////////////////////////////////////////////

Local_Environment::Local_Environment()
{}

Local_Environment::~Local_Environment()
{}

void Local_Environment::print(ostream & file_buffer)
{
	map<string, Eval_Result *>::iterator i;
	for (i = variable_table.begin(); i != variable_table.end(); i++)
	{
		Eval_Result * vi = variable_table[(*i).first];
		if (vi != NULL)
		{
			if (vi->is_variable_defined() == false)
				file_buffer << VAR_SPACE << (*i).first << " : undefined" << "\n";
		
			else if(vi->get_result_enum() == int_result || vi->get_result_enum() == bool_result) 
				file_buffer << VAR_SPACE << (*i).first << " : " << vi->get_int_value() << "\n";
			
			else if(vi->get_result_enum() == float_result) 
			  file_buffer << VAR_SPACE << (*i).first << " : " << std::fixed << std::setprecision(2) << vi->get_value_float() << "\n";
		}
	}
}

bool Local_Environment::is_variable_defined(string name)
{
	Eval_Result * i = variable_table[name];
	if (i != NULL) {
		return i->is_variable_defined();
	}
	else
		return false;
}

Eval_Result * Local_Environment::get_variable_value(string name)
{
	Eval_Result * i = variable_table[name];
	return i;
}

void Local_Environment::put_variable_value(Eval_Result & i, string name)
{
	variable_table[name] = &i; 
}

bool Local_Environment::does_variable_exist(string name)
{
	if (variable_table[name] == NULL)
		return false;
	else
		return true;
}

   
