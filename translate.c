#include <stdio.h>
#include "util.h"
#include "symbol.h"
#include "types.h"
#include "temp.h"
#include "frame.h"
#include "translate.h"
#include "tree.h"

static void display_l(Tr_level l);
static void display_ac(Tr_access ac);

/******************对一些结构体的定义******************/
//每一个level的具体信息
struct Tr_level_ {
	Tr_level parent;
	Temp_label name;
	F_frame frame;
	Tr_accessList formals;
};

//每一个局部变量在帧栈里的信息
struct Tr_access_ {
	Tr_level level;
	F_access access;
};

struct Cx{
	patchList trues;
	patchList falses;
	T_stm stm;
};

struct Tr_exp_{
	enum{Tr_ex, Tr_nx, Tr_cx}kind;
	union{
		T_exp ex;
		T_stm nx;
		struct Cx cx;
	}u;
};

struct patchList_ {
	Temp_label *head;
	patchList tail;
};

struct Tr_expList_{
	Tr_exp head;
	Tr_expList tail;
};

/************关于patchList的一些函数************/
//patchList的构造
static patchList PatchList(Temp_label *tp, patchList pl){
	patchList new=checked_malloc(sizeof(struct patchList_));
	new->head=tp;
	new->tail=pl;
	return new;
}

//将label赋值给标号回填表里的label地址
static void doPatch(patchList pl, Temp_label label){
	while(pl){
		*(pl->head)=label;
		pl=pl->tail;
	}
}

/************Tr_类型和T_类型的转换**************/
//T_exp转换为Tr_exp
static Tr_exp Tr_Ex(T_exp exp){
	Tr_exp new=checked_malloc(sizeof(struct Tr_exp_));
	new->kind=Tr_ex;
	new->u.ex=exp;
	return new;
}

//将T_stm转换为Tr_exp
static Tr_exp Tr_Nx(T_stm stm){
	Tr_exp new=checked_malloc(sizeof(struct Tr_exp_));
	new->kind=Tr_nx;
	new->u.nx=stm;
	return new;
}

//将条件语句转换为Tr_exp
static Tr_exp Tr_Cx(patchList trues, patchList falses, T_stm stm){
	Tr_exp new=checked_malloc(sizeof(struct Tr_exp_));
	new->kind=Tr_cx;
	new->u.cx.trues=trues;
	new->u.cx.falses=falses;
	new->u.cx.stm=stm;
	return new;
}

//将Tr_exp转为T_exp
T_exp unEx(Tr_exp e){
	switch(e->kind){
		case Tr_ex:
			return e->u.ex;
		case Tr_cx:{
			Temp_temp r=Temp_newtemp();
			Temp_label t=Temp_newlabel(), f=Temp_newlabel();
			doPatch(e->u.cx.trues, t);
			doPatch(e->u.cx.falses, f);
			return T_Eseq(T_Move(T_Temp(r), T_Const(1)),
					      T_Eseq(e->u.cx.stm,
							     T_Eseq(T_Label(f),
									    T_Eseq(T_Move(T_Temp(r), T_Const(0)),
											   T_Eseq(T_Label(t), T_Temp(r))))));
			}
		case Tr_nx:
			return T_Eseq(e->u.nx, T_Const(0));
	}
	assert(0);
}

//将Tr_exp转为T_stm
static T_stm unNx(Tr_exp e){
	switch(e->kind){
		case Tr_ex:
			return T_Exp(e->u.ex);
		case Tr_nx:
			return e->u.nx;
		case Tr_cx:{
			Temp_temp r = Temp_newtemp(); 
			Temp_label t = Temp_newlabel(), f = Temp_newlabel(); 
			doPatch(e->u.cx.trues, t);
			doPatch(e->u.cx.falses, f);
			return T_Exp(T_Eseq(T_Move(T_Temp(r), T_Const(1)),
					            T_Eseq(e->u.cx.stm,
							           T_Eseq(T_Label(f),
									          T_Eseq(T_Move(T_Temp(r), T_Const(0)),
											         T_Eseq(T_Label(t), T_Temp(r)))))));

		}
	}
	assert(0);
}

//将Tr_exp转为条件语句
static struct Cx unCx(Tr_exp e){
	switch (e->kind) {
		case Tr_cx:
			return e->u.cx;
		case Tr_ex: {
			struct Cx cx;
			cx.stm = T_Cjump(T_ne, e->u.ex, T_Const(0), NULL, NULL);
			cx.trues = PatchList(&(cx.stm->u.CJUMP.true), NULL);
			cx.falses = PatchList(&(cx.stm->u.CJUMP.false), NULL);
			return cx;
		}
		case Tr_nx:
			assert(0); 
	}
	assert(0);
}

//将Tr_expList转换为T_expList
static T_expList Tr_expList_convert(Tr_expList l) {
	T_expList h = NULL, t = NULL;
	while(l) {
		T_exp tmp = unEx(l->head);
		if (h) {
			t->tail =  T_ExpList(tmp, NULL);
			t = t->tail;
		} else {
			h = T_ExpList(tmp, NULL);
			t = h;
		}
		l=l->tail;
	}
	return h;
}

/****************栈帧部分**********************/
//构造Tr_access
static Tr_access Tr_Access(Tr_level level, F_access ac) {
	Tr_access T_ac = checked_malloc(sizeof(struct Tr_access_));
	T_ac->level  = level;
	T_ac->access = ac;
	return T_ac;
}

//Tr_accessList的构造
Tr_accessList Tr_AccessList(Tr_access ac, Tr_accessList al) {
	Tr_accessList new_al = checked_malloc(sizeof(struct Tr_accessList_));
	new_al->head = ac;
	new_al->tail = al;
	return new_al;
} 


Tr_level Tr_newLevel(Tr_level parent, Temp_label name, U_boolList formals){
	Tr_accessList head, tail;
	F_accessList  alist; 
	Tr_access a;
	Tr_level l = checked_malloc(sizeof(*l));
	
	head=tail=NULL;
	l->parent = parent;
	l->name = name;
	l->frame = F_newFrame(name, U_BoolList(TRUE,formals));	
	for (alist= F_formals(l->frame)->tail; alist; alist = alist->tail) {
		a = Tr_Access(l, alist->head);
		if (head) {
			tail->tail = Tr_AccessList(a, NULL);
			tail = tail->tail;
		} else {
			head = Tr_AccessList(a, NULL);
			tail = head;
		}
	}
	l->formals = head;
	#ifdef F_P
	display_l(l);
	#endif
	return l;
}

static Tr_level outer = NULL;	//保存最外层的level
//返回最外层level
Tr_level Tr_outermost(void) {
	if (!outer) outer = Tr_newLevel(NULL, Temp_newlabel(), NULL);
	return outer;
}

//给其它函数调用，返回level的formals
Tr_accessList Tr_formals(Tr_level l) {
	return l->formals;
}

//在栈帧中分配一个变量
Tr_access Tr_allocLocal(Tr_level l, bool escape) {
	Tr_access ac = checked_malloc(sizeof(struct Tr_access_));
	ac->level = l;
	ac->access = F_allocLocal(l->frame, escape);
	return ac;
}

/**************各种类型的操作******************/
//把Tr_exp加入到Tr_expList中
Tr_expList Tr_ExpList(Tr_exp h, Tr_expList t) {
    Tr_expList l = checked_malloc(sizeof(struct Tr_expList_));
	l->head = h;
	l->tail = t;
	return l;
}

//将h作为expList的新head
void Tr_expList_prepend(Tr_exp h, Tr_expList * l) {
	Tr_expList newhead = Tr_ExpList(h, NULL);
	newhead->tail = *l;
	*l = newhead;
}

//取得一个简单变量的值
Tr_exp Tr_simpleVar(Tr_access ac, Tr_level l) {
	T_exp fp = T_Temp(F_FP()); 
	while (l != ac->level) { 
		F_access sl = F_formals(l->frame)->head;
		fp = F_Exp(sl, fp);
		l = l->parent;
	}
	return Tr_Ex(F_Exp(ac->access,fp)); 
}

//base+offs来寻址
Tr_exp Tr_fieldVar(Tr_exp base, int off) {
	return Tr_Ex(T_Mem(T_Binop(T_plus, unEx(base), T_Const(off * F_WORD_SIZE))));
}

//用一个表达式来作为偏移量
Tr_exp Tr_subscriptVar(Tr_exp base, Tr_exp index) {
	return Tr_Ex(T_Mem(T_Binop(T_plus,unEx(base),T_Binop(T_mul,unEx(index),T_Const(F_WORD_SIZE)))));
}

//整数
Tr_exp Tr_intExp(int i) {
	return Tr_Ex(T_Const(i));
}

//空寄存器
static Temp_temp nilTemp = NULL;
Tr_exp Tr_nilExp() {
	if (!nilTemp) {
		nilTemp = Temp_newtemp(); 
		T_stm alloc = T_Move(T_Temp(nilTemp),F_externalCall(String("initRecord"), T_ExpList(T_Const(0), NULL)));
		return Tr_Ex(T_Eseq(alloc, T_Temp(nilTemp)));
	}
	return Tr_Ex(T_Temp(nilTemp));
}


Tr_exp Tr_noExp() {
	return Tr_Ex(T_Const(0));
}

//分配一段空间，并将exp放进去
Tr_exp Tr_recordExp(int n, Tr_expList l) {
	Temp_temp r = Temp_newtemp();
	T_stm alloc = T_Move(T_Temp(r),F_externalCall(String("initRecord"), T_ExpList(T_Const(n * F_WORD_SIZE), NULL)));
	if(l!=NULL){
		int i = n - 1;
		T_stm seq = T_Move(T_Mem(T_Binop(T_plus, T_Temp(r), T_Const(i-- * F_WORD_SIZE))), unEx(l->head));
		for (l = l->tail; l; l = l->tail, i--) {
			seq = T_Seq(T_Move(T_Mem(T_Binop(T_plus, T_Temp(r), T_Const(i * F_WORD_SIZE))), unEx(l->head)),seq);
		}
		return Tr_Ex(T_Eseq(T_Seq(alloc, seq), T_Temp(r)));
	}
	else
		return Tr_Ex(T_Eseq(alloc, T_Temp(r)));
}
	
//分配数组并且初始化值
Tr_exp Tr_arrayExp(Tr_exp size, Tr_exp init) {
	return Tr_Ex(F_externalCall(String("initArray"), T_ExpList(unEx(size), T_ExpList(unEx(init), NULL))));
}

//将expList里的东西，从后向左执行，返回第一个值
Tr_exp Tr_seqExp(Tr_expList l) {
	T_exp resl = unEx(l->head); 
	for (l = l->tail; l; l = l->tail) {
		resl = T_Eseq(T_Exp(unEx(l->head)), resl);
	}
	return Tr_Ex(resl);
}

Tr_exp Tr_doneExp() { 
	return Tr_Ex(T_Name(Temp_newlabel())); 
}

//while循环，结束后返回0
Tr_exp Tr_whileExp(Tr_exp test, Tr_exp body, Tr_exp done) {
	Temp_label testl = Temp_newlabel(), bodyl = Temp_newlabel();
	return Tr_Ex(T_Eseq(T_Jump(T_Name(testl), Temp_LabelList(testl, NULL)), 
				        T_Eseq(T_Label(bodyl),
							   T_Eseq(unNx(body),
								      T_Eseq(T_Label(testl),
								             T_Eseq(T_Cjump(T_eq, unEx(test), T_Const(0), unEx(done)->u.NAME, bodyl),
										            T_Eseq(T_Label(unEx(done)->u.NAME), T_Const(0))))))));
}

//赋值操作
Tr_exp Tr_assignExp(Tr_exp lval, Tr_exp exp) { 
	return Tr_Nx(T_Move(unEx(lval), unEx(exp))); 
}

//跳转到b里的位置
Tr_exp Tr_breakExp(Tr_exp b) { 
	return Tr_Nx(T_Jump(T_Name(unEx(b)->u.NAME), Temp_LabelList(unEx(b)->u.NAME, NULL))); 
}

//数学操作
Tr_exp Tr_arithExp(A_oper op, Tr_exp left, Tr_exp right) { 
	T_binOp opp;
	switch(op) {
		case A_plusOp  : opp = T_plus; break;
		case A_minusOp : opp = T_minus; break;
		case A_timesOp : opp = T_mul; break;
		case A_divideOp: opp = T_div; break;
		default: assert(0);
	}
	return Tr_Ex(T_Binop(opp, unEx(left), unEx(right)));
}

//判断两个表达式的关系
Tr_exp Tr_relExp(A_oper op, Tr_exp left, Tr_exp right) {
    T_relOp oper;
	switch(op) {
		case A_ltOp: oper = T_lt; break;
		case A_leOp: oper = T_le; break;
		case A_gtOp: oper = T_gt; break;
		case A_geOp: oper = T_ge; break;
		case A_eqOp: oper = T_eq; break;
		case A_neqOp: oper = T_ne; break;
		default: assert(0); 
	}
	T_stm cond = T_Cjump(oper, unEx(left), unEx(right), NULL, NULL);
	patchList trues = PatchList(&cond->u.CJUMP.true, NULL);
	patchList falses = PatchList(&cond->u.CJUMP.false, NULL);
	return Tr_Cx(trues, falses, cond);
}

//判断字符串是否相等
Tr_exp Tr_eqStringExp(A_oper op, Tr_exp left, Tr_exp right) {
	T_exp resl = F_externalCall(String("stringEqual"), T_ExpList(unEx(left), T_ExpList(unEx(right), NULL)));
	if (op == A_eqOp) return Tr_Ex(resl);
	else if (op == A_neqOp){
		T_exp e = (resl->kind == T_CONST && resl->u.CONST != 0) ? T_Const(0): T_Const(1);
		return Tr_Ex(e);
	} else {
		if (op == A_ltOp) return (resl->u.CONST < 0) ? Tr_Ex(T_Const(0)) : Tr_Ex(T_Const(1));
		else return (resl->u.CONST > 0) ? Tr_Ex(T_Const(0)) : Tr_Ex(T_Const(1));
	}
}

//对if表达式的判断
Tr_exp Tr_ifExp(Tr_exp test, Tr_exp then, Tr_exp elsee) {
	Tr_exp result = NULL;
	Temp_label t = Temp_newlabel(), f = Temp_newlabel(), finish = Temp_newlabel();
	struct Cx cond = unCx(test);
	doPatch(cond.trues, t);
	doPatch(cond.falses, f);

	T_stm thenStm;
	if (then->kind == Tr_ex) 
		thenStm = T_Exp(then->u.ex);
	else 
		thenStm = (then->kind == Tr_nx) ? then->u.nx : then->u.cx.stm;

	if (!elsee) {
		result = Tr_Nx(T_Seq(cond.stm, T_Seq(T_Label(t),T_Seq(thenStm, T_Label(f))))); 
	} 
	else {
		T_stm elseeStm;
		if (elsee->kind == Tr_ex) 
			elseeStm = T_Exp(elsee->u.ex);
		else 
			elseeStm = (elsee->kind == Tr_nx) ? elsee->u.nx : elsee->u.cx.stm;	

		T_stm finishJump = T_Jump(T_Name(finish), Temp_LabelList(finish, NULL));
		result = Tr_Nx(T_Seq(cond.stm, 
					         T_Seq(T_Label(t), 
								   T_Seq(thenStm,
									     T_Seq(finishJump, 
											   T_Seq(T_Label(f),
							                         T_Seq(elseeStm, T_Label(finish)))))))); 
	}
	return result;
}

//获得静态链
static Tr_exp Tr_StaticLink(Tr_level now, Tr_level def) {
	T_exp addr = T_Temp(F_FP());
	while(now != def->parent) {
		F_access sl = F_formals(now->frame)->head;
		addr = F_Exp(sl, addr);
		now = now->parent;
	}
	return Tr_Ex(addr);
}

//函数调用
Tr_exp Tr_callExp(Temp_label label, Tr_level fun, Tr_level call, Tr_expList * l) {
	T_expList args = NULL;
	Tr_expList_prepend(Tr_StaticLink(call, fun), l);
	args = Tr_expList_convert(*l);
	return Tr_Ex(T_Call(T_Name(label), args));
}

static F_fragList fragList= NULL;
void Tr_procEntryExit(Tr_level level, Tr_exp body) {
	F_frag procfrag = F_ProcFrag(unNx(body), level->frame);
	fragList = F_FragList(procfrag, fragList);
}

static F_fragList stringFragList = NULL;
Tr_exp Tr_stringExp(string s) { 
	Temp_label slabel = Temp_newlabel();
	F_frag fragment = F_StringFrag(slabel, s);
	stringFragList = F_FragList(fragment, stringFragList);
	return Tr_Ex(T_Name(slabel));
}

//会改变stringFragList，所以好像只能用一次
F_fragList Tr_getResult() {
	F_fragList cur = NULL, prev = NULL;
	for (cur = stringFragList; cur; cur = cur->tail)
		prev = cur;
	if (prev) prev->tail = fragList;
	return stringFragList ? stringFragList : fragList;
} 

/*******************debug函数****************************/


void test_Tr_expList_prepend(Tr_expList l) {
	while(l) {
		printf("Tr_exp->type: %d\n", l->head->kind);
		l = l->tail;
	}
}
//@@@
void test_T_expList(T_expList l) {
	while(l) {
		printf("T_exp->type: %d\n", l->head->kind);
		l = l->tail;
	}
} 

static void display_l(Tr_level l) {
	static int lnum;
	if (l->parent) {
		printf("parent: %s\n", Temp_labelstring(l->parent->name));
	} else {
		printf("parent: root\n");
	}
	printf("addr: %s\n", Temp_labelstring(l->name));
	display_f(l->frame);
}

static void display_ac(Tr_access ac) {
	printf("level: %s\n", Temp_labelstring(ac->level->name));	
	dis_ac(ac->access);
}

T_exp public_unEx(Tr_exp e) {
	return unEx(e);
}
T_stm public_unNx(Tr_exp e) {
	return unNx(e);
}
//@@@ print Tr_exp
void print(Tr_exp et, FILE * out) {
    if (et->kind == Tr_ex) printExp(unEx(et), out);
	if (et->kind == Tr_nx) printStm(unNx(et), out);
	if (et->kind == Tr_cx) printStm(unCx(et).stm, out);
} 

void print_frag(F_fragList fl, FILE * out) {
	if (!fl) {
		puts("fragList is NULL");
		return;
	}
	while (fl) {
		F_frag f = fl->head;
		switch(f->kind) {
		case F_stringFrag:
			print(Tr_Ex(T_Name(f->u.stringg.label)), out);
			fprintf(out, ":%s\n",f->u.stringg.str);
			break;
		case F_procFrag:
            fprintf(out, "\n函数%s\n",f->u.proc.frame->name->name);
			print(Tr_Nx(f->u.proc.body), out);
			break;
		default: assert(0 && "frag-kind is error");
		}
		fl = fl->tail;
	}
}

