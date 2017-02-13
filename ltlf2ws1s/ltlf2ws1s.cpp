/*
 * added by Shufang ZHU on Jan 10th, 2017
 * translate ltlf formulas to ws1s, the input of MONA
*/

#include "ltlf2ws1s.h"
#include <stdlib.h>
#include <stdio.h>
#include <ctype.h>
#include <set>
#include <assert.h>
#include <iostream>
#include <fstream>
#include <boost/algorithm/string.hpp>

using namespace std;
#define MAXN 1000000


void ltlf2ws1s (ltl_formula *root)
{
  int c = 1;
  trans_ws1s(root, 1, c);
  set<string> P = get_alphabet (root);
  if(!P.empty()){
    cout<<"var2 ALIVE, ";
    print_alphabet_no_comma(root);
    cout<<";"<<endl;
  }
  cout<<"0 in ALIVE;"<<endl;
  cout<<"export(\"tmp.dfa\", F1(0, ALIVE";
  print_alphabet(root);
  cout<<"));"<<endl;

}

void print_alphabet_no_comma (ltl_formula* root){
  set<string> P = get_alphabet (root);
  if(!P.empty()){
    set<string>::iterator it = P.begin ();
    // cout<<toupper(*it);
    cout<<up(*it);
    it++;
    while (it != P.end ()){
      cout<<", "<<up(*it);
      it++;
    }
  }
}

void print_alphabet (ltl_formula* root){
  set<string> P = get_alphabet (root);
  if(!P.empty()){
    set<string>::iterator it = P.begin ();
    // cout<<toupper(*it);
    cout<<", "<<up(*it);
    it++;
    while (it != P.end ()){
      cout<<", "<<up(*it);
      it++;
    }
  }
}

void print_alphabet_not (ltl_formula* root){
  set<string> P = get_alphabet (root);
  if(!P.empty()){
    set<string>::iterator it = P.begin ();
    // cout<<toupper(*it);
    cout<<", "<<up(*it)<<"\\{p}";
    it++;
    while (it != P.end ()){
      cout<<", "<<up(*it);
      it++;
    }
  }
}

void printvars (ltl_formula* root){
  set<string> P = get_alphabet (root);
  if(!P.empty()){
    set<string>::iterator it = P.begin ();
    // cout<<toupper(*it);
    cout<<", var2 "<<up(*it);
    it++;
    while (it != P.end ()){
      cout<<", var2 "<<up(*it);
      it++;
    }
  }
}

void trans_ws1s(ltl_formula* root, int t, int& c){
  int cur;
  switch(root->_type)
  {
        case eNOT:
          c = c + 1;
          cur = c;
          trans_ws1s(root->_right, cur, c);
          cout<<"# F"<<t<<" denotes "<<to_string (root).c_str ()<<endl;
          cout<<"pred F"<<t<<" (var1 p, var2 ALIVE";
          printvars(root);
          cout<<") = "<<endl;
          cout<<"     ~F"<<cur<<" (p, ALIVE";
          print_alphabet(root->_right);
          cout<<")"<<endl;
          cout<<"       & (p in ALIVE)"<<endl;
          cout<<"       & all1 l:(l <= p => l in ALIVE);"<<endl<<endl;
          break;
        case eNEXT:
          c = c + 1;
          cur = c;
          trans_ws1s(root->_right, cur, c);
          cout<<"# F"<<t<<" denotes "<<to_string (root).c_str ()<<endl;
          cout<<"pred F"<<t<<" (var1 p, var2 ALIVE";
          printvars(root);
          cout<<") = "<<endl;
          cout<<"     p >= 0 & F"<<cur<<" (p+1, ALIVE";
          print_alphabet(root->_right);
          cout<<");"<<endl<<endl;
          break;
        case eFUTURE:
          c = c + 1;
          cur = c;
          trans_ws1s(root->_right, cur, c);
          cout<<"# F"<<t<<" denotes "<<to_string (root).c_str ()<<endl;
          cout<<"pred F"<<t<<" (var1 p, var2 ALIVE";
          printvars(root);
          cout<<") = "<<endl;
          cout<<"     ex1 q:( q >= p"<<endl;
          cout<<"             & F"<<cur<<" (q, ALIVE";
          print_alphabet(root->_right);
          cout<<")"<<endl;
          cout<<"            );"<<endl<<endl;
          break;
        case eUNTIL:
          c = c + 2;
          cur = c;
          trans_ws1s(root->_right, cur-1, c);
          trans_ws1s(root->_left, cur, c);
          cout<<"# F"<<t<<" denotes "<<to_string (root).c_str ()<<endl;
          cout<<"pred F"<<t<<" (var1 p, var2 ALIVE";
          printvars(root);
          cout<<") = "<<endl;
          cout<<"     ex1 q:( q >= p"<<endl;
          cout<<             "& F"<<cur-1<<" (q, ALIVE";
          print_alphabet(root->_right);
          cout<<")"<<endl;
          cout<<"             &"<<endl;
          cout<<"             all1 k:(p<= k & k < q) => F"<<cur<<" (k, ALIVE";
          print_alphabet(root->_left);
          cout<<")"<<endl;
          cout<<"            );"<<endl<<endl;
          break;
        case eOR:
          c = c + 2;
          cur = c;
          trans_ws1s(root->_right, cur-1, c);
          trans_ws1s(root->_left, cur, c);
          cout<<"# F"<<t<<" denotes "<<to_string (root).c_str ()<<endl;
          cout<<"pred F"<<t<<" (var1 p, var2 ALIVE";
          printvars(root);
          cout<<") = "<<endl;
          cout<<"     F"<<cur-1<<" (p, ALIVE";
          print_alphabet(root->_right);
          cout<<")"<<endl;
          cout<<"     |"<<endl;
          cout<<"     F"<<cur<<" (p, ALIVE";
          print_alphabet(root->_left);
          cout<<");"<<endl<<endl;
          break;
        case eTRUE:
          cout<<"# F"<<t<<" denotes TRUE "<<to_string (root).c_str ()<<endl;
          cout<<"pred F"<<t<<" (var1 p, var2 ALIVE) = "<<endl;
          cout<<"     true;"<<endl<<endl;
          break;
        case eFALSE:
          cout<<"# F"<<t<<" denotes TRUE "<<to_string (root).c_str ()<<endl;
          cout<<"pred F"<<t<<" (var1 p, var2 ALIVE) = "<<endl;
          cout<<"     false;"<<endl<<endl;
          break;
        case 3:
          cout<<"# F"<<t<<" denotes Atom "<<to_string (root).c_str ()<<endl;
          cout<<"pred F"<<t<<" (var1 p, var2 ALIVE";
          printvars(root);
          cout<<") = "<<endl;
          cout<<"     p >= 0 & p in ";
          print_alphabet_no_comma(root);
          cout<<" & p in ALIVE"<<endl;
          cout<<"     & all1 l:(l <= p => l in ALIVE);"<<endl<<endl;
          break;
        default:
          break;
  }
}

string up(string a){
  return boost::to_upper_copy<std::string>(a);
}



char in[MAXN];

int main (int argc, char ** argv)
{
  /*if (argc == 1)
    {
      puts ("#please input the formula:");
      if (fgets (in, MAXN, stdin) == NULL)
      {
        printf ("Error: read input!\n");
        exit (0);
      }
    }
  else
    {*/
		string StrLine;
		std::string input;
		assert(argc == 2);
		input = argv[1];
		ifstream myfile(input);
		if (!myfile.is_open()) //判断文件是否存在及可读
		{
		    printf("error!");
		    return -1;
		}
		getline(myfile, StrLine);
		myfile.close(); //关闭文件
      //strcpy (in, StrLine);
    printf ("#%s\n", in);
   // }
    ltl_formula *root = getAST (StrLine.c_str());
    ltl_formula *newroot = bnf (root);
    printf ("#%s\n", to_string (root).c_str ());
    printf ("#%s\n", to_string (newroot).c_str ());
    ltlf2ws1s (newroot);

    // printf ("%s\n", res.c_str ());
    destroy_formula (root);
    destroy_formula (newroot);
}






