#ifndef TIGER_PRINTTREE_H_
#define TIGER_PRINTTREE_H_

/* function prototype from printtree.c */
void printStmList(FILE * out, T_stmList stmList);
void printExp(T_exp, FILE * out);
void printStm(T_stm, FILE * out);
void pr_tree_exp(FILE *out, T_exp exp, int d);
#endif /* TIGER_PRINTTREE_H_ */


