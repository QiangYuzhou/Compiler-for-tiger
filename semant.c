#include <stdio.h>
#include "util.h"
#include "errormsg.h"
#include "symbol.h"
#include "absyn.h"
#include "types.h"
#include "temp.h"
#include "translate.h"
#include "env.h"
#include "semant.h"
#include "tree.h"
#include "printtree.h"
struct expty transVar(Tr_level level, Tr_exp breakk,S_table venv, S_table tenv, A_var v);
struct expty transExp(Tr_level level, Tr_exp breakk,S_table venv, S_table tenv, A_exp a);
Tr_exp  transDec(Tr_level level, Tr_exp breakk,S_table venv, S_table tenv, A_dec d);
Ty_ty transTy(S_table tenv, A_ty a);
Ty_ty actual_ty(Ty_ty ty);
bool match_ty(Ty_ty ty1, Ty_ty ty2);

struct expty expTy(Tr_exp exp, Ty_ty ty){
	struct expty e;
	e.exp = exp;
	e.ty = ty;
	return e;
}

Ty_ty actual_ty(Ty_ty ty){
	if(!ty)
		return ty;
	if(ty->kind == Ty_name)
		return actual_ty(ty->u.name.ty);
	else 
		return ty;
}

bool match_ty(Ty_ty ty1, Ty_ty ty2){
	Ty_ty aty1 = actual_ty(ty1);
	Ty_ty aty2 = actual_ty(ty2);
	return (((aty1->kind == Ty_record || aty1->kind == Ty_array) && aty1==aty2) ||
			(aty1->kind == Ty_record && aty2->kind == Ty_nil) ||
			(aty1->kind == Ty_nil && aty2->kind == Ty_record) ||
			(aty1->kind != Ty_record && aty1->kind != Ty_array && aty1->kind == aty2->kind));
}

Ty_ty transTy(S_table table, A_ty ty) {
	Ty_ty t, t2;
	Ty_fieldList tlist, thead;
	A_fieldList f;
	Ty_field tftemp;

	t=NULL;
	switch (ty->kind) {
	case A_nameTy:{
		t = S_look(table, ty->u.name);
		if (!t) {
			EM_error(ty->pos, "undefined type %s", S_name(ty->u.name));
			return Ty_Int();
		}
		return t;
	}break;
	case A_recordTy:{
	tlist=thead=NULL;
		for(f = ty->u.record; f; f = f->tail){
			t2 = S_look(table, f->head->typ);
			if(!t2)
				EM_error(f->head->pos, "undefined type %s", S_name(f->head->typ));
			else{
				tftemp = Ty_Field(f->head->name,t2);
				if(!tlist){
					tlist = Ty_FieldList(tftemp, NULL);
					thead = tlist;
				}
				else{
					tlist->tail = Ty_FieldList(tftemp, NULL);
					tlist = tlist->tail;
				}
			}
		}
		tlist = thead;
		return Ty_Record(tlist);
	}break;
	case A_arrayTy:{
		t = S_look(table, ty->u.array);
		if (!t) 
			EM_error(ty->pos, "undefined type %s", S_name(ty->u.array));
		return Ty_Array(t);
	}break;
	default:
		assert(0);
	}
}
					

struct expty transVar(Tr_level level,Tr_exp breakk, S_table venv, S_table tenv, A_var v)
{
	if (!v) {
		return expTy(Tr_noExp(), Ty_Void());
	}
	E_enventry x;
	struct expty e, e2;
	Ty_fieldList list;
	Tr_exp result=Tr_noExp();

	switch(v->kind){
		case A_simpleVar:{
			x = S_look(venv, v->u.simple);
			if(x && x->kind == E_varEntry){
				result=Tr_simpleVar(x->u.var.access, level);
				return expTy(result, actual_ty(x->u.var.ty));
			}
			else{
				EM_error(v->pos, "undefined variable %s", S_name(v->u.simple));
				return expTy(result, Ty_Int());
			}
		}break;
		case A_fieldVar:{
			e = transVar(level, breakk, venv, tenv, v->u.field.var);
			if(e.ty->kind != Ty_record){
				EM_error(v->pos, "wrong record type");
				return expTy(result,Ty_Record(NULL));			
			}
			else{
				int i=0;
				for(list = e.ty->u.record;list;list=list->tail,i++){
					if(list->head->name == v->u.field.sym)
						result=Tr_fieldVar(e.exp,i);
						return expTy(result,actual_ty(list->head->ty));
				}
				EM_error(v->pos, "no such field: %s in the record ", S_name(v->u.field.sym));
			}
			return expTy(result, Ty_Record(NULL));
		}break;
		case A_subscriptVar:{
			e = transVar(level,breakk, venv, tenv, v->u.subscript.var);
			if(e.ty-> kind != Ty_array){
				EM_error(v->pos, "wrong array type");
				return expTy(result, Ty_Array(NULL));
			}
			else{
				e2 = transExp(level, breakk, venv, tenv, v->u.subscript.exp);
				if(e2.ty->kind != Ty_int)
					EM_error(v->pos, "array index has to be int");
				else{
					result=Tr_subscriptVar(e.exp,e2.exp);
					return expTy(result, actual_ty(e.ty->u.array));
				}
			}
			return expTy(result, Ty_Array(NULL));
		}break;
		default:
			assert(0);
	}
}

struct expty transExp(Tr_level level, Tr_exp breakk, S_table venv, S_table tenv, A_exp a)
{
	E_enventry call;
	A_expList argslist, list;
	Ty_tyList formlist;
	struct expty t, left, right, variable, expression, ifcon, ifthen, ifelse, whilecon, whilebody, lo, hi, body, arraysize, arrayinit, exp;
	A_oper oper;
	Ty_ty recordty, arrayty;
	Ty_fieldList fieldlist;
	A_efieldList elist;
	A_decList d;
	int stop = 0;
	Tr_exp result=Tr_noExp();

	if (!a) { 
		return expTy(Tr_noExp(), Ty_Void()); 
	}
	switch(a->kind){
		case A_varExp: 
			return transVar(level,breakk, venv,tenv,a->u.var);break;
		case A_nilExp: 
			return expTy(Tr_nilExp(), Ty_Nil());break;
		case A_intExp:
			return expTy(Tr_intExp(a->u.intt), Ty_Int());break;
		case A_doubleExp:
			return expTy(Tr_intExp(a->u.intt), Ty_Double());break;
		case A_stringExp:
			return expTy(Tr_stringExp(a->u.stringg), Ty_String());break;
		case A_callExp:{
			A_expList args = NULL;
			Tr_expList argList = NULL;
			call = S_look(venv,a->u.call.func);
			for (args = a->u.call.args; args; args = args->tail) { 
				struct expty arg = transExp(level, breakk, venv, tenv, args->head);
	            Tr_expList_prepend(arg.exp, &argList);			
			}
			if(call && call->kind == E_funEntry){
				result = Tr_callExp(call->u.fun.label, call->u.fun.level, level, &argList);
				argslist = a->u.call.args;
				formlist = call->u.fun.formals;
				while (argslist && formlist) {
					t = transExp(level, breakk, venv, tenv, argslist->head);
					if (!match_ty(t.ty, formlist->head)){
						EM_error(a->pos, "unmatched params in function %s\n", S_name(a->u.call.func));
						stop = 1;
						break;					
					}
					argslist = argslist->tail;
					formlist = formlist->tail;
				}
				if(stop == 1);
				else if (argslist && !formlist) 
					EM_error(a->pos, "too many parameters in function %s\n", S_name(a->u.call.func));
				else if (!argslist && formlist) 
					EM_error(a->pos, "too few parameters in function %s\n", S_name(a->u.call.func));
				else {
					if(call->u.fun.result)
						return expTy(result,actual_ty(call->u.fun.result));
					else 
						return expTy(Tr_noExp(),Ty_Void());
				}
			}
			else 
				EM_error(a->pos, "undefined function %s", S_name(a->u.call.func));
			return expTy(result, Ty_Void());
		}break;
		case A_opExp:{
			oper = a->u.op.oper;
			left = transExp(level, breakk,venv, tenv, a->u.op.left);
			right = transExp(level, breakk,venv, tenv, a->u.op.right);
			if(oper==A_plusOp || oper==A_minusOp || oper==A_timesOp || oper==A_divideOp){
				if(left.ty->kind != Ty_int && left.ty->kind != Ty_double)
					EM_error(a->u.op.left->pos,"integer or double required");
				if(right.ty->kind != Ty_int && right.ty->kind != Ty_double)
					EM_error(a->u.op.right->pos,"integer or double required");
				if(left.ty->kind == Ty_int && right.ty->kind == Ty_int && oper != A_timesOp)
					return expTy(Tr_arithExp(oper, left.exp, right.exp), Ty_Int());
				else
					return expTy(Tr_arithExp(oper, left.exp, right.exp), Ty_Int());
			}
			else if(oper==A_eqOp || oper==A_neqOp || oper==A_ltOp || oper==A_leOp ||
				oper==A_gtOp || oper==A_geOp){
				if(oper == A_eqOp || oper == A_neqOp){
					/*if(left.ty->kind == Ty_record && right.ty->kind == Ty_nil)
						return expTy(NULL, Ty_Int());
					if(right.ty->kind == Ty_record && left.ty->kind == Ty_nil)
						return expTy(NULL, Ty_Int());*/
					switch(left.ty->kind) {
					case Ty_int:
					case Ty_double:
						if (right.ty->kind == Ty_int || right.ty->kind == Ty_double) result = Tr_relExp(oper, left.exp, right.exp);
						else {EM_error(a->u.op.right->pos, "unexpected type in comparsion");}
						break;
					case Ty_string:
						if (match_ty(right.ty, left.ty)) result = Tr_eqStringExp(oper, left.exp, right.exp);
						else {EM_error(a->u.op.right->pos, "unexpected type in comparsion");}
						break;
					case Ty_array:
						if (match_ty(right.ty, left.ty)) result = Tr_relExp(oper, left.exp, right.exp);
						else {EM_error(a->u.op.right->pos, "unexpected type in comparsion");}
					    break;
					case Ty_record:
						if (match_ty(right.ty, left.ty) || right.ty->kind == Ty_nil) result = Tr_relExp(oper, left.exp, right.exp);
						else {EM_error(a->u.op.right->pos, "unexpected type in comparsion");}
						break;
					default:
						EM_error(a->u.op.right->pos, "unexpected expression in comparsion");
					}
					return expTy(result, Ty_Int());
				}
				else {
					switch(left.ty->kind) {
					case Ty_double:
					case Ty_int:
						if (right.ty->kind == Ty_double || right.ty->kind == Ty_int) result = Tr_relExp(oper, left.exp, right.exp); 
						else {EM_error(a->u.op.right->pos, "unexpected type in comparsion");}
						break;
					case Ty_string:
						if (right.ty->kind == Ty_string) result = Tr_eqStringExp(oper, left.exp, right.exp);
						else {EM_error(a->u.op.right->pos, "unexpected type in comparsion");}
						break;
					default:
						EM_error(a->u.op.right->pos, "unexpected type in comparsion");
					}
					return expTy(result, Ty_Int());
				}
			}
			else
				assert(0);	
		}break;
		case A_recordExp:{
			recordty = actual_ty(S_look(tenv, a->u.record.typ));
			if(!recordty)
				EM_error(a->pos,"undefined type %s", S_name(a->u.record.typ));
			else{
				if(recordty->kind != Ty_record){
					EM_error(a->pos, "wrong record type %s", S_name(a->u.record.typ));
					return expTy(Tr_noExp(), Ty_Record(NULL));
				}
				else{
						fieldlist = recordty->u.record;
						elist = a->u.record.fields;
						while(fieldlist && elist){
							t = transExp(level, breakk,venv, tenv, elist->head->exp);
							if(!(fieldlist->head->name == elist->head->name) || !match_ty(fieldlist->head->ty, t.ty)){
								EM_error(a->pos, "unmatched name: %s", S_name(a->u.record.typ));
								stop = 1;
								break;
							}
							fieldlist=fieldlist->tail;
							elist= elist->tail;
						}
						if(stop == 1);
						else if(fieldlist && !elist)
							EM_error(a->pos, "too few fields in %s", S_name(a->u.record.typ));
						else if(!fieldlist && elist)
							EM_error(a->pos, "too many fields in %s", S_name(a->u.record.typ));
						else{
							Tr_expList l = NULL;
							int n = 0;
							A_efieldList el;
							for (el = a->u.record.fields; el; el = el->tail, n++) {
								struct expty val = transExp(level, breakk, venv, tenv, el->head->exp);	
								Tr_expList_prepend(val.exp, &l);
							}
							return expTy(Tr_recordExp(n,l), recordty);
						}
				}
			}
			return expTy(Tr_noExp(), Ty_Record(NULL));
		}break;
		case A_seqExp:{
			Tr_expList l = NULL;
			list = a->u.seq;
			struct expty seqone;
			if(!list)
				return expTy(Tr_noExp(),Ty_Void());
			else{
				while(list){
					seqone=transExp(level, breakk,venv, tenv, list->head);
					Tr_expList_prepend(seqone.exp, &l);
                    list=list->tail;
				}
				return expTy(Tr_seqExp(l), seqone.ty);
			}
		}break;
		case A_assignExp:{
			variable = transVar(level,breakk, venv, tenv, a->u.assign.var);
			expression = transExp(level, breakk,venv, tenv, a->u.assign.exp);
			if(!match_ty(variable.ty, expression.ty))
				EM_error(a->pos, "unmatched assign");
			return expTy(Tr_assignExp(variable.exp,expression.exp), Ty_Void());
		}break;
		case A_ifExp:{
			ifcon = transExp(level, breakk,venv, tenv, a->u.iff.test);
			ifthen = transExp(level, breakk,venv, tenv, a->u.iff.then);
			ifelse =expTy(NULL,NULL);
			if(a->u.iff.elsee){
				ifelse = transExp(level, breakk,venv, tenv, a->u.iff.elsee);
				if(ifcon.ty->kind != Ty_int)
					EM_error(a->u.iff.test->pos, "if condition type should be int");
				else if(!match_ty(ifthen.ty, ifelse.ty))
					EM_error(a->pos, "if else expression return different types");
			}
			return expTy(Tr_ifExp(ifcon.exp, ifthen.exp, ifelse.exp), ifthen.ty);
		}break;
		case A_whileExp:{
			whilecon = transExp(level, breakk, venv, tenv, a->u.whilee.test);
			if(whilecon.ty->kind != Ty_int)
				EM_error(a->pos, "while condition type should be int");
			Tr_exp done = Tr_doneExp();
			struct expty body = transExp(level, done, venv, tenv, a->u.whilee.body);
			return expTy(Tr_whileExp(whilecon.exp, body.exp, done), Ty_Void());
		}break;
		case A_forExp:{
			lo = transExp(level,breakk, venv, tenv, a->u.forr.lo);
			hi = transExp(level,breakk, venv, tenv, a->u.forr.hi);
            Tr_access access=Tr_allocLocal(<#Tr_level l#>, <#bool e#>)
			if(lo.ty != Ty_Int() || hi.ty != Ty_Int())
				EM_error(a->pos, "range type should be int");
            S_enter(venv, a->u.forr.var, E_VarEntry(Ty_Int()));
			S_beginScope(venv);
			transDec(level,breakk, venv, tenv, A_VarDec(a->pos,a->u.forr.var, S_Symbol("int"), a->u.forr.lo));
			body = transExp(level, breakk,venv, tenv, a->u.forr.body);
			S_endScope(venv);
			return expTy(NULL, Ty_Void());
		}break;
		case A_breakExp:{
			if (!breakk) 
				return expTy(Tr_noExp(), Ty_Void());
			return expTy(Tr_breakExp(breakk), Ty_Void());
		}
		case A_letExp:{
			A_decList decs;
			Tr_expList l = NULL;
			S_beginScope(venv);
			S_beginScope(tenv);
			for(d = a->u.let.decs; d; d= d->tail)
				Tr_expList_prepend(transDec(level, breakk,venv, tenv, d->head),&l);
			exp = transExp(level, breakk,venv, tenv, a->u.let.body);
			Tr_expList_prepend(exp.exp, &l);
			S_endScope(venv);
			S_endScope(tenv);
			return expTy(Tr_seqExp(l), exp.ty);
		}break;
		case A_arrayExp:{
			arrayty = actual_ty(S_look(tenv, a->u.array.typ));
			if(!arrayty){
				EM_error(a->pos, "undefined array type %s", S_name(a->u.array.typ));
				return expTy(Tr_noExp(), Ty_Array(NULL));
			}
			else if(arrayty->kind != Ty_array){
				EM_error(a->pos, "wrong array type %s", S_name(a->u.array.typ));
				return expTy(Tr_noExp(), Ty_Array(NULL));
			}
			arraysize = transExp(level, breakk, venv, tenv, a->u.array.size);
			arrayinit = transExp(level, breakk, venv, tenv, a->u.array.init);
			if(arraysize.ty->kind != Ty_int)
				EM_error(a->pos, "array size should be int");
			else if (!match_ty(arrayinit.ty, arrayty->u.array))
				EM_error(a->pos, "init type should be same as array type", S_name(a->u.array.typ));
			else
				return expTy(Tr_arrayExp(arraysize.exp,arrayinit.exp), arrayty);
			return expTy(Tr_noExp(), Ty_Array(NULL));
		}break;
		default:
			assert(0);
	}
}

Tr_exp transDec(Tr_level level, Tr_exp breakk,S_table venv, S_table tenv, A_dec d){
	struct expty e;
	Ty_ty t, t2, nt;
	A_fundecList funclist;
	A_fundec f;
	Ty_tyList tlist, head, list;
	A_fieldList flist, fieldlist;
	E_enventry x, funentry;
	A_nametyList nlist;
	Ty_fieldList tflist, tfhead;
	Ty_field tftemp;
	int iscyl = 1;
	Temp_label funLabel;
	Tr_accessList alist;
	Tr_access a;
	Tr_level l;
	U_boolList bhead, btail;

	switch(d->kind){
		case A_varDec:{
			e = transExp(level, breakk, venv, tenv, d->u.var.init);
			/*#ifdef F_P
			puts("->:");
			printf("id: %s\n", S_name(d->u.var.var));
			#endif*/
			a = Tr_allocLocal(level, d->u.var.escape);
			if(!d->u.var.typ){
				if(e.ty->kind == Ty_nil || e.ty->kind == Ty_void){
					EM_error(d->pos, "init should not be nil", S_name(d->u.var.var));
					S_enter(venv, d->u.var.var, E_VarEntry(a, Ty_Int()));
				}
				else 
					S_enter(venv, d->u.var.var, E_VarEntry(a, e.ty));
			}
			else{
				t = S_look(tenv, d->u.var.typ);
				if(!t)
					EM_error(d->pos, "undefined type %s", S_name(d->u.var.typ));
				else{
					if(!match_ty(t, e.ty))
						EM_error(d->pos, "unmatched type %s", S_name(d->u.var.typ));
					S_enter(venv, d->u.var.var, E_VarEntry(a, t));
				}
			}
			return Tr_assignExp(Tr_simpleVar(a, level), e.exp);
		}break;
		case A_functionDec:{
			for(funclist = d->u.function; funclist; funclist = funclist->tail){
				if(funclist->head->result){
					t = S_look(tenv, funclist->head->result);
					if(!t){
						EM_error(funclist->head->pos, "undefined return type");
						t = Ty_Void();
					}

				}
				else
					t = Ty_Void();
				tlist = NULL;
				head = tlist;		
				for(flist = funclist->head->params;flist;flist = flist->tail){
					t2= S_look(tenv,flist->head->typ);
					if(!t2){
						EM_error(flist->head->pos, "undefined type %s", S_name(flist->head->typ));
						t2= Ty_Int();
					}
					if(!tlist){
						tlist = Ty_TyList(t2,NULL);
						head = tlist;
					}
					else{
						tlist->tail = Ty_TyList(t2,NULL);
						tlist = tlist->tail;
					}
				}
				tlist = head;
				funLabel = Temp_newlabel();
				#ifdef F_P
				puts("-------------------");
				printf("function: %s\n", S_name(funclist->head->name));
				#endif
				bhead= btail = NULL;			
				for(fieldlist = funclist->head->params; fieldlist; fieldlist=fieldlist->tail){
					if(!bhead){
						bhead = U_BoolList(TRUE, NULL);
						btail = bhead;
					}
					else{
						btail->tail = U_BoolList(TRUE, NULL);
						btail = btail->tail;
					}
				}
				l = Tr_newLevel(level, funLabel, bhead);
				S_enter(venv, funclist->head->name, E_FunEntry(l, funLabel, tlist, t));
			}
			for(funclist = d->u.function; funclist; funclist= funclist->tail){
				f= funclist->head;
				funentry = S_look(venv, f->name);
				S_beginScope(venv);
				tlist = funentry->u.fun.formals;
				alist = Tr_formals(funentry->u.fun.level);
				for(flist = f->params, list = tlist; flist && list && alist; flist= flist->tail, list= list->tail, alist= alist->tail)
					S_enter(venv, flist->head->name, E_VarEntry(alist->head, list->head));
				e = transExp(funentry->u.fun.level, breakk,venv, tenv, f->body);
				x = S_look(venv, f->name);
				if(!match_ty(funentry->u.fun.result, e.ty))
					EM_error(f->pos, "wrong return type in function %s", S_name(f->name));
				Tr_procEntryExit(funentry->u.fun.level, e.exp);
				S_endScope(venv);
			}
			return Tr_noExp();
		}break;
		case A_typeDec:{
			for(nlist = d->u.type; nlist; nlist= nlist->tail)
				S_enter(tenv, nlist->head->name, Ty_Name(nlist->head->name,NULL));
			iscyl = 1;
			for(nlist = d->u.type; nlist; nlist= nlist->tail){
				t = transTy(tenv, nlist->head->ty);
				if(iscyl == 1)
					if(t->kind != Ty_name)
						iscyl = 0;
				if(!nlist->tail && t->kind != Ty_name && t->kind != Ty_record && t->kind != Ty_array)
					EM_error(d->pos, "actual type should be declared before");
				nt = S_look(tenv, nlist->head->name);
				nt->u.name.ty = t;
			}
			if(iscyl == 1)
				EM_error(d->pos, "illegal type");	
			return Tr_noExp();	
		}break;
		default:
			assert(0);
	}
}

F_fragList  SEM_transProg(A_exp exp){
	struct expty t;
	S_table venv = E_base_venv();
	S_table tenv = E_base_tenv();
    FILE * f1 = fopen("tree.txt", "w");
	t = transExp(Tr_outermost(), NULL,venv, tenv, exp);
    pr_tree_exp(f1,unEx(t.exp),0);
    fclose(f1);
	F_fragList resl = Tr_getResult();
	return resl;
}
