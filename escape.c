/*this model must before semant model*/
#include "symbol.h"
#include "absyn.h"
static void transExp(S_table env, int depth, A_exp e);
static void transDec(S_table env, int depth, A_dec d);
static void transVar(S_table env, int depth, A_var v);
