/*
 * added by Jianwen LI on December 26th, 2014
 * translate ltlf formulas to smv
*/

#ifndef LTL_2_SMV_H
#define LTL_2_SMV_H

#include "ltl_formula.h"
#include "trans.h"
#include "utility.h"
#include <string>
#include <set>
#include <map>

/*
 * translate ltlf formula to smv
*/
std::string ltlf2smv (ltl_formula*);   //original encoding with the original input

/*
 *translate ltlf formula to boolean transition system in smv
*/
std::string ltlf2tran (ltl_formula*, std::set<std::string>&);  //original encoding with the original input

/*
 * translate ltlf formula to smv
*/
std::string ltlf2smv_2 (ltl_formula*);   //bnf encoding (in another look at LTL model checking)

/*
 *translate ltlf formula to boolean transition system in smv
*/
void ltlf2trans_2 (ltl_formula*, std::string&, std::string&, std::set<std::string>&);  //bnf encoding (in another look at LTL model checking)

/*
 *get the boolean expr for given formula
*/
std::string get_expr (ltl_formula*, std::set<std::string>&);

/*
 * get the var for ltlf formula
*/
std::string get_var (ltl_formula*);

void ltlf2ws1s (ltl_formula*);

void trans_ws1s (ltl_formula*, int, int&);

void printvars (ltl_formula*);

void print_alphabet (ltl_formula*);
std::string up(std::string);

/*
 *create ltl spec for smv
*/
std::string get_ltlspec (std::set<std::string>);



static int id_num = 0;
static std::map<std::string, std::string> VARS;
static std::set<std::string> already_exists;


#endif
