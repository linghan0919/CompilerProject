%{
	
	#include <stdio.h>
	#include <stdlib.h>
	#include <string.h>
	#include <assert.h>
	#include <stdarg.h>
	#include <string.h>
      
	void yyerror(char *s);

	struct Node
	{
		char name[100];
		char type[10];
		int line;
		int value;
		struct Node *son;
		struct Node *bro;
	};

	FILE *ifile,*ofile;

	//Flags
	int regNum = 0;
	int stEleNum = 0;
	int paraFlag = 0;
	int BlockLevel = 0;
	int rFlag = 0; 
	int wFlag = 0;
	int readFlag = 0;
	int tfFlag = -1;
	int exDecFlag = 0;
	int paraNum = 0;
	int tempReg = 0;
	char funcName[10];
	struct Node *nodeFlag = NULL;
	int arrFlag = 0;
	int returnFlag = 0;

	char *paraArr[10];
	struct Node *root;
	struct Node *makeTree(char *n,int num,...)
	{
		struct Node *p=(struct Node*)malloc(sizeof(struct Node));
		strcpy(p->name,n);
		strcpy(p->type,"N-T");
		va_list argPtr;
		va_start(argPtr,num);
		//printf("self:%s,<%s>\n",p->name,p->type);
		p->son=va_arg(argPtr, struct Node *);
		//printf("   son:%s,<%s>\n",(p->son)->name,(p->son)->type);
		p->bro=NULL;
		{
			int i;
			struct Node *tmp;
			tmp=p->son;
			for(i=1;i<num;++i)
			{
				tmp->bro=va_arg(argPtr, struct Node *);
				tmp=tmp->bro;
			}
		}
		va_end(argPtr);
		return p;
	}
	
	struct Node *empty(char *n)
	{
		struct Node *p=(struct Node*)malloc(sizeof(struct Node));
		strcpy(p->name,n);
		strcpy(p->type,"N-T");
		p->son=NULL;
		p->bro=NULL;
		//printf("Empty Node!");
		return p;
		
	}

	struct symbol	//For VAR
	{
		char *head;
		char word[100];
		char type;  // 'g'lobal 'l'ocal 'a'rg 'e'lement 's'tuct
		int size;  // for arrays
		char st[100];   // sturct name
		int stno; // the loc in a struct
		int reg; // reg location
		int mem; // mem location
	};

	struct symbol* symTable[27][20];  //27=26letters + _

	void DFS(struct Node *r,int l);

	void showHead();
	void showFoot();

	void _PROGRAM(struct Node *root);
	void _EXTDEFS(struct Node *n);
	void _EXTDEF(struct Node *n);
	void _EXTVARSTYPE(struct Node *n);	
	void _DEFSSTRUCT(struct Node *n,char *stname);	
	void _DEFSTRUCT(struct Node *n,char *stname);
	void _VARNOINIT(struct Node *n);
	void _VARINIT(struct Node *n);
	void _FUNC(struct Node *n);
	void _ARGSINIT(struct Node *n);
	void _PARAS(struct Node *n);
	void _PARA(struct Node *n);
	void _STMTBLOCK(struct Node *n);
	void _STMTS(struct Node *n);
	void _STMT(struct Node *n);
	void _IFAND(struct Node *n);
	void _DEFS(struct Node *n);		
	void _DEF(struct Node *n);
	void _DECS(struct Node *n);		
	void _DECEX(struct Node *n);	
	void _DECIN(struct Node *n);	
	char* _EXP(struct Node *n);
	void _BOP(struct Node *n);
	void _FEXP(struct Node *n);
	void _ARGSFUNC(struct Node *n);

	void _EXTDEFSTRUCT(struct Node *n);
%}
	

%union{
	struct Node* node;
	}
	
%token <node> IF
%token <node> THEN
%token <node> ELSE
%token <node> STRUCT
%token <node> RETURN
%token <node> BREAK
%token <node> CONT
%token <node> FOR
%token <node> TYPE
%token <node> ID
%token <node> INT
%token <node> COMMA  
%token <node> SEMI
%token <node> LC RC

%type <node> PROGRAM
%type <node> EXTDEFS
%type <node> EXTDEF
%type <node> EXTVARS
%type <node> SPEC
%type <node> STSPEC
%type <node> OPTTAG
%type <node> VAR
%type <node> FUNC
%type <node> PARAS
%type <node> PARA
%type <node> STMTBLOCK
%type <node> STMTS
%type <node> STMT
%type <node> ESTMT
%type <node> DEFS
%type <node> DEF
%type <node> DECS
%type <node> DEC
%type <node> INIT
%type <node> EXP
%type <node> FEXP
%type <node> ARRS
%type <node> ARGS

%right <node> ASSIGNOP
%left <node> LOR
%left <node> LAND
%left <node> BOR
%left <node> BXOR
%left <node> BAND
%left <node> EQU NE
%left <node> COMP
%left <node> SHIFT
%left <node> LBOP
%left <node> HBOP
%right <node> LNOT PIN PDE BNOT
%left <node> LP RP LB RB DOT

%%

/*程序*/
PROGRAM :EXTDEFS               /*程序->外部定义*/
	{$$=makeTree("PROGRAM",1,$1);root=$$;}
	;

/*外部定义集*/		
EXTDEFS : EXTDEF EXTDEFS  {$$=makeTree("EXTDEFS",2,$1,$2);}
	| /*empty*/  {$$=empty("EXTDEFS");}
	;	

/*外部定义*/		
EXTDEF : SPEC EXTVARS SEMI       /*如：int a;*/
	{$$=makeTree("EXTDEF",3,$1,$2,$3);}
	| SPEC FUNC STMTBLOCK	/*如：void function {}*/
	{$$=makeTree("EXTDEF",3,$1,$2,$3);}
	;

/*外部变量*/		
EXTVARS : DEC					/*声明*/
	{$$=makeTree("EXTVARS",1,$1);
	 if($1==nodeFlag)nodeFlag=NULL;}
	| DEC COMMA EXTVARS		/*声明 声明……*/
	{$$=makeTree("EXTVARS",3,$1,$2,$3);}
	| /*empty*/
	{$$=empty("EXTVARS");}
	;

/*规格*/
SPEC : TYPE						/*类型*/
	{$$=makeTree("SPEC",1,$1);}
	| STSPEC					/*结构体类型*/
	{$$=makeTree("SPEC",1,$1);}
	;

/*结构体*/	 
STSPEC : STRUCT OPTTAG LC DEFS RC	/*STRUCT 可选标签{定义}*/ 
	{$$=makeTree("STSPEC",5,$1,$2,$3,$4,$5);}
	| STRUCT ID	
	{$$=makeTree("STSPEC",2,$1,$2);}
	;

/*可选的标签*/
OPTTAG :  ID
	{$$=makeTree("OPTTAG",1,$1);}
	| /*empty*/
	{$$=empty("OPTTAG");}
	;
	
/*变量*/
VAR : ID
	{$$=makeTree("VAR",1,$1);}
	| VAR LB INT RB     /*变量[int]   数组*/
	{$$=makeTree("VAR",4,$1,$2,$3,$4);arrFlag=1;}
	| VAR DOT ID		
	{$$=makeTree("VAR",3,$1,$2,$3);}
	;

/*函数声明*/
FUNC : ID LP PARAS RP	/*标识符  (参数列表)*/
	{$$=makeTree("FUNC",4,$1,$2,$3,$4);
	 if(strcmp($1->name,"main")) strcpy(funcName,$1->name);}
	;

/*参数列表*/
PARAS : PARA COMMA PARAS	/*参,参……*/
	{$$=makeTree("PARAS",3,$1,$2,$3);}
	| PARA
	{$$=makeTree("PARAS",1,$1);}
	| /*empty*/
	{$$=empty("PARAS");}
	;

/*参数*/
PARA : SPEC VAR			/*类型 变量名*/
	{$$=makeTree("PARA",2,$1,$2);}
	;

/*语句块*/
STMTBLOCK : LC DEFS STMTS RC	/*{定义们，语句们}*/
	  {$$=makeTree("STMTBLOCK",4,$1,$2,$3,$4);}
	  ;

/*语句集*/
STMTS : STMT STMTS		/*语句 语句……*/
	{$$=makeTree("STMTS",2,$1,$2);}
	| /*empty*/
	{$$=empty("STMTS");}
	;

/*语句*/
STMT : EXP SEMI			/*表达式;*/
	{$$=makeTree("STMT",2,$1,$2);}
	| STMTBLOCK			/*语句块*/
	{$$=makeTree("STMT",1,$1);}
	| RETURN EXP SEMI		/*return 表达式;*/
	{$$=makeTree("STMT",3,$1,$2,$3);}
	| IF LP EXP RP STMT ESTMT		/*if (表达式)语句 else语句*/
	{$$=makeTree("STMT",6,$1,$2,$3,$4,$5,$6);}
	| FOR LP FEXP SEMI FEXP SEMI FEXP RP STMT	/*for(表达式;表;表）语句*/
	{$$=makeTree("STMT",9,$1,$2,$3,$4,$5,$6,$7,$8,$9);}
	| CONT SEMI		/*continue；*/
	{$$=makeTree("STMT",2,$1,$2);}
	| BREAK SEMI	/*break;*/
	{$$=makeTree("STMT",2,$1,$2);}
	;

/*ELSE中的语句*/	
ESTMT : ELSE STMT
	{$$=makeTree("ESTMT",2,$1,$2);}
      |/*empty*/
	{$$=empty("ESTMT");}
      ;

/*定义集合*/	  
DEFS : DEF DEFS
	{$$=makeTree("DEFS",2,$1,$2);}
	| /*empty*/
	{$$=empty("DEFS");}
	;

/*定义*/
DEF : SPEC DECS SEMI	/*类型 声明;*/
	{$$=makeTree("DEF",3,$1,$2,$3);}
	;

/*声明S*/
DECS : DEC COMMA DECS	/*声明,声明……*/
	{$$=makeTree("DECS",3,$1,$2,$3);}
     | DEC
	{$$=makeTree("DECS",1,$1);}
     ;

/*声明*/
DEC : VAR
	{$$=makeTree("DEC",1,$1);}
	| VAR ASSIGNOP INIT		/*变量 = 初始值*/
	{$$=makeTree("DEC",3,$1,$2,$3);
	 if(arrFlag==1)nodeFlag = $$;arrFlag=0;}
	;

/*初始化*/
INIT : EXP			/*表达式*/
	{$$=makeTree("INIT",1,$1);}
	| LC ARGS RC	/*{变量}  用于给数组赋初值*/
	{$$=makeTree("INIT",3,$1,$2,$3);}
	;

/*不可以为空的表达式*/
EXP : EXP HBOP EXP		
	{$$=makeTree("EXP",3,$1,$2,$3);}
	|EXP LBOP EXP		
	{$$=makeTree("EXP",3,$1,$2,$3);}
	|EXP SHIFT EXP		
	{$$=makeTree("EXP",3,$1,$2,$3);}
	|EXP COMP EXP		
	{$$=makeTree("EXP",3,$1,$2,$3);}
	|EXP EQU EXP		
	{$$=makeTree("EXP",3,$1,$2,$3);}
	|EXP NE EXP		
	{$$=makeTree("EXP",3,$1,$2,$3);}
	|EXP BAND EXP		
	{$$=makeTree("EXP",3,$1,$2,$3);}
	|EXP BXOR EXP		
	{$$=makeTree("EXP",3,$1,$2,$3);}
	|EXP BOR EXP		
	{$$=makeTree("EXP",3,$1,$2,$3);}
	|EXP LAND EXP		
	{$$=makeTree("EXP",3,$1,$2,$3);}
	|EXP LOR EXP		
	{$$=makeTree("EXP",3,$1,$2,$3);}
	| LNOT EXP			
	{$$=makeTree("EXP",2,$1,$2);}
	| PIN EXP				
	{$$=makeTree("EXP",2,$1,$2);}
	| PDE EXP			
	{$$=makeTree("EXP",2,$1,$2);}
	| BNOT EXP			
	{$$=makeTree("EXP",2,$1,$2);}
	| LBOP EXP			
	{$$=makeTree("EXP",2,$1,$2);}
	| LP EXP RP				/*(表达式)*/
	{$$=makeTree("EXP",3,$1,$2,$3);}
	| ID LP ARGS RP			/*标识符 (变量);*/
	{$$=makeTree("EXP",4,$1,$2,$3,$4);
         if(!strcmp($1->name,"read"))rFlag=1; 
	 if(!strcmp($1->name,"write"))wFlag=1;}
	| ID ARRS				/*标识符 [i][j]…… 用于数组*/
	{$$=makeTree("EXP",2,$1,$2);}
	| ID ARRS ASSIGNOP EXP				
	{$$=makeTree("EXP",4,$1,$2,$3,$4);}
	| EXP DOT ID			/*表达式.标识符  用于结构体中东西*/
	{$$=makeTree("EXP",3,$1,$2,$3);}
	| EXP DOT ID ASSIGNOP EXP			
	{$$=makeTree("EXP",5,$1,$2,$3,$4,$5);}
	| INT					/*整型数*/
	{$$=makeTree("EXP",1,$1);}
	;


FEXP : EXP
	{$$=makeTree("FEXP",1,$1);}
	| /*empty*/
	{$$=empty("FEXP");}
	;
	
/*数列的参数*/
ARRS : LB EXP RB ARRS		/*[][]……*/
	{$$=makeTree("ARRS",4,$1,$2,$3,$4);}
	| /*empty*/
	{$$=empty("ARRS");}
	;

/*参数*/
ARGS : EXP COMMA ARGS		/*表达式,表达式*/
	{$$=makeTree("ARGS",3,$1,$2,$3);}
	| EXP
	{$$=makeTree("ARGS",1,$1);}
	;

%%
void yyerror(char *s)
{
	printf(">>Error:%s\n",s);
	exit(1);
}

int main(int argc,char **argv)
{
	//FILE *ifile,*ofile;
	if((ifile=freopen(argv[1],"r",stdin))==NULL)
	{
		fprintf(stderr,"The file <%s> cannot be opened.\n",argv[1]);
		return 0;
	}

	if((ofile=freopen(argv[2],"w+",stdout))==NULL)
	{
		fprintf(stderr,"The file <%s> cannot be opened.\n",argv[2]);
		return 0;
	}
	
	//yy_switch_to_buffer(yy_scan_string("int try;"));
	if(!yyparse())
	{
		int layer=0;
		//printf("PARSE SUCCESS!\n\n");
		//DFS(root,layer);
		printf("; ModuleID = '%s'\n",argv[1]);
		_PROGRAM(root);
	}
	else
	{
		printf("PARSE ERROR!\n");
	}
	fclose(ifile);
	fclose(ofile);
	return 0;
}

void DFS(struct Node *r,int l)
{
	if(r==NULL)return;
	int i;
	for(i=0;i<l;++i)printf("-----");
	printf("%s <%s>,%d",r->name,r->type,r->value);
	if(r->son!=NULL)
	{
		printf("\n");
		DFS(r->son,l+1);
	}
	else 
	{
	   	if(r->line!=0)printf("<line:%d>\n",r->line);
	   	else printf("\n");
	}
	
	DFS(r->bro,l);

}

void showHead()
{
	printf("target datalayout = \"e-p:64:64:64-i1:8:8-i8:8:8-i16:16:16-i32:32:32-i64:64:64-f32:32:32-f64:64:64-v64:64:64-v128:128:128-a0:0:64-s0:64:64-f80:128:128-n8:16:32:64-S128\"\n");
	printf("target triple = \"x86_64-pc-linux-gnu\"\n\n");

	if(nodeFlag!=NULL)
	{
		_DECIN(nodeFlag);
		printf("\n; Function Attrs: nounwind\n");
		printf("declare void @llvm.memcpy.p0i8.p0i8.i64(i8* nocapture, i8* nocapture readonly, i64, i32, i1) #2\n\n");
	 	nodeFlag=NULL;
	}

	if(rFlag==1 || wFlag==1)
		printf("@.str = private unnamed_addr constant [3 x i8] c\"%%d\\00\", align 1\n");

}

void showFoot()
{
	if(rFlag==1)
		printf("\ndeclare i32 @__isoc99_scanf(i8*, ...) #1\n");
	if(wFlag==1)
		printf("\ndeclare i32 @printf(i8*, ...) #1\n");

	printf("\nattributes #0 = { nounwind uwtable \"less-precise-fpmad\"=\"false\" \"no-frame-pointer-elim\"=\"true\" \"no-frame-pointer-elim-non-leaf\" \"no-infs-fp-math\"=\"false\" \"no-nans-fp-math\"=\"false\" \"stack-protector-buffer-size\"=\"8\" \"unsafe-fp-math\"=\"false\" \"use-soft-float\"=\"false\" }\n" );

	if(rFlag==1 || wFlag==1)
	printf("attributes #1 = { \"less-precise-fpmad\"=\"false\" \"no-frame-pointer-elim\"=\"true\" \"no-frame-pointer-elim-non-leaf\" \"no-infs-fp-math\"=\"false\" \"no-nans-fp-math\"=\"false\" \"stack-protector-buffer-size\"=\"8\" \"unsafe-fp-math\"=\"false\" \"use-soft-float\"=\"false\" }\n");

	printf("\n!llvm.ident = !{!0}\n");
	printf("\n!0 = metadata !{metadata !\"Ubuntu clang version 3.4-1ubuntu3 (tags/RELEASE_34/final) (based on LLVM 3.4)\"}");
}

void _PROGRAM(struct Node *root)
{
	
	showHead();

	_EXTDEFS(root->son);
	
	showFoot();
}

void _EXTDEFS(struct Node *n)
{
	BlockLevel=0;
	if(n->son==NULL) return;
	struct Node *p=n->son;
	_EXTDEF(p);
	_EXTDEFS(p->bro);
}

void _EXTDEF(struct Node *n)
{
	struct Node *son1=n->son;
	struct Node *son2=son1->bro;
	struct Node *son3=son2->bro;
	
	if(!strcmp(son2->name,"EXTVARS")) //SPEC EXTVARS SEMI
	{
		struct Node *son11=son1->son;  //TYPE or STSPEC
		if(!strcmp(son11->name,"int"))	 //int ...
			_EXTVARSTYPE(son2);
		else	//struct ...
			_EXTDEFSTRUCT(n);		
	}
	else //SPEC FUNC STMTBLOCK
	{	
		_FUNC(son2);
		_STMTBLOCK(son3);
	}	
}

void _EXTVARSTYPE(struct Node *n)
{
	if(n->son==NULL) return;
	if(n->son->bro==NULL) //DEC
		_DECEX(n->son);
	else //DEC COMMA EXTVARS
	{
		_DECEX(n->son);
		_EXTVARSTYPE(n->son->bro->bro);
	}
}

void _DECEX(struct Node *n)
{
	exDecFlag=1;
	if(n->son->bro==NULL) //VAR
		_VARNOINIT(n->son);
		
	
	else//VAR ASSIGNOP INIT
		_VARINIT(n->son);	
	exDecFlag=0;
}

void _EXTDEFSTRUCT(struct Node *n)
{
	struct Node *stspec=n->son->son;
	
	struct Node *stname=stspec->son->bro;
	if(stname->bro==NULL) //STRUCT ID
	{
		char *stid=(char*)malloc(sizeof(char)*100);
		stid=stname->name;
		
		struct Node *tmp=n->son;
		
		while(tmp)
		{
			char *id=(char*)malloc(sizeof(char)*100);
			id=tmp->bro->son->son->son->name;
			
			int group;
			group=id[0]-'a';
			if(group<0)group=id[0]-'A';
			if(id[0]=='_')group=26;

			int i=0;	
			while(symTable[group][i]) i++;
		symTable[group][i]=(struct symbol*)malloc(sizeof(struct symbol));
			struct symbol *sym=symTable[group][i];

			sym->head=(char*)malloc(sizeof(char));
			strcpy(sym->head,"@");
			strcpy(sym->word,id);
			strcpy(sym->st,stid);
			sym->type='e'; // struct element
	
	    printf("@%s = common global %%struct.%s zeroinitializer, align 4\n",
			id,stid);
			
			tmp=tmp->bro->son->bro;
		}
		
	}
	else // STRUCT OPTTAG { DEFS }
	{
		char *id=(char*)malloc(sizeof(char)*100);
		id=stname->son->name;

		int group;
		group=id[0]-'a';
		if(group<0)group=id[0]-'A';
		if(id[0]=='_')group=26;

		int i=0;	
		while(symTable[group][i]) i++;
		symTable[group][i]=(struct symbol*)malloc(sizeof(struct symbol));
		struct symbol *sym=symTable[group][i];

		sym->head=(char*)malloc(10*sizeof(char));
		strcpy(sym->head,"%struct.");
		strcpy(sym->word,id);
		sym->type='s';
		
		printf("%s%s = type {",sym->head,sym->word);
		stEleNum=0;
		_DEFSSTRUCT(stname->bro->bro,id);
		printf(" }\n");
	}
		
}

void _DEFSSTRUCT(struct Node *n,char *stname)
{
	if(n->son==NULL)return;
	else
	{		
		_DEFSTRUCT(n->son,stname);
		_DEFSSTRUCT(n->son->bro,stname);
	}
}

void _DEFSTRUCT(struct Node *n,char *stname)
{
	struct Node *dec = n->son->bro->son;

	char *id=(char*)malloc(sizeof(char)*100);
	id=dec->son->son->name;

	int group;
	group=id[0]-'a';
	if(group<0)group=id[0]-'A';
	if(id[0]=='_')group=26;

	int i=0;	
	while(symTable[group][i]) i++;
	symTable[group][i]=(struct symbol*)malloc(sizeof(struct symbol));
	struct symbol *sym=symTable[group][i];

	strcpy(sym->word,id);
	strcpy(sym->st,stname);
	sym->type='i'; // in struct
	sym->stno=stEleNum;
	if(stEleNum==0)
		printf(" i32");
	else
		printf(", i32");	
	stEleNum++;
	
}

void _VARNOINIT(struct Node *n)
{
	if(n->son->bro==NULL)  //ID
	{
		char *id=(char*)malloc(sizeof(char)*100);
		id=n->son->name;

		// store the new var in symTable
		int group;
		group=id[0]-'a';
		if(group<0)group=id[0]-'A';
		if(id[0]=='_')group=26;

		int i=0;	
		while(symTable[group][i]) i++;
		symTable[group][i]=(struct symbol*)malloc(sizeof(struct symbol));
		struct symbol *sym=symTable[group][i];
		
		if(exDecFlag==0) // DECIN
		{
			sym->head=(char*)malloc(sizeof(char));
			strcpy(sym->head,"%");
			strcpy(sym->word,id);
			sym->type = 'l';  //local
		printf("  %s%s = alloca i32, align 4\n",sym->head,sym->word);
		}
		else // DECEX
		{
			sym->head=(char*)malloc(sizeof(char));
			strcpy(sym->head,"@");
			strcpy(sym->word,id);
			sym->type = 'g';  //global
	printf("%s%s = common global i32 0, align 4\n",sym->head,sym->word); 			}
	}
	else // VAR [ INT ]
	{
		int num = n->son->bro->bro->value;

		char *id=(char*)malloc(sizeof(char)*100);
		id=n->son->son->name;

		// store the new var in symTable
		int group;
		group=id[0]-'a';
		if(group<0)group=id[0]-'A';
		if(id[0]=='_')group=26;

		int i=0;	
		while(symTable[group][i]) i++;
		symTable[group][i]=(struct symbol*)malloc(sizeof(struct symbol));
		struct symbol *sym=symTable[group][i];
		sym->size=num;

		if(exDecFlag==0) // DECIN
		{
			sym->head=(char*)malloc(sizeof(char));
			strcpy(sym->head,"%");
			strcpy(sym->word,id);
			sym->type = 'l';  //local
		printf("  %s%s = alloca [%d x i32], align 4\n",
				sym->head,sym->word,num);
		}

		else // DECEX
		{
			sym->head=(char*)malloc(sizeof(char));
			strcpy(sym->head,"@");
			strcpy(sym->word,id);
			sym->type = 'g';  //global
	printf("%s%s = common global [%d x i32] zeroinitializer, align 4\n",
				sym->head,sym->word,num); 			
		}
		
	}
}

void _VARINIT(struct Node *n)
{
	struct Node *init=n->bro->bro;

	if(n->son->bro==NULL)  //ID = INIT
	{
		int value = init->son->son->value;
		char *id=(char*)malloc(sizeof(char)*100);
		id=n->son->name;

		// store the new var in symTable
		int group;
		group=id[0]-'a';
		if(group<0)group=id[0]-'A';
		if(id[0]=='_')group=26;

		int i=0;	
		while(symTable[group][i]) i++;
		symTable[group][i]=(struct symbol*)malloc(sizeof(struct symbol));
		struct symbol *sym=symTable[group][i];
		
		if(exDecFlag==0) // DECIN
		{
			sym->head=(char*)malloc(sizeof(char));
			strcpy(sym->head,"%");
			strcpy(sym->word,id);
			sym->type = 'l';  //local
		printf("  %s%s = alloca i32, align 4\n",sym->head,sym->word);
		printf("  store i32 %d, i32* %s%s, align 4\n",
				value,sym->head,sym->word);
		}
		else // DECEX
		{
			sym->head=(char*)malloc(sizeof(char));
			strcpy(sym->head,"@");
			strcpy(sym->word,id);
			sym->type = 'g';  //global
	printf("%s%s = global i32 %d, align 4\n",sym->head,sym->word,value); 			}
	}

	else  // VAR [ INT ] = INIT
	{
		int num = n->son->bro->bro->value;

		char *id=(char*)malloc(sizeof(char)*100);
		id=n->son->son->name;

		// store the new var in symTable
		int group;
		group=id[0]-'a';
		if(group<0)group=id[0]-'A';
		if(id[0]=='_')group=26;

		int i=0;	
		while(symTable[group][i]) i++;
		symTable[group][i]=(struct symbol*)malloc(sizeof(struct symbol));
		struct symbol *sym=symTable[group][i];
		sym->size=num;

		if(exDecFlag==0) // DECIN
		{
			sym->head=(char*)malloc(sizeof(char));
			strcpy(sym->head,"%");
			strcpy(sym->word,id);
			sym->type = 'l';  //local
		        
			if(nodeFlag!=NULL) // first declare
			{
		printf("\n@%s.%s = private unnamed_addr constant [%d x i32] [",
				funcName, sym->word, num);
				_ARGSINIT(init->son->bro);
				printf("], align 4\n");
			}

			else // declare inside function 
			{
			printf("  %s%s = alloca [%d x i32], align 4\n",
					sym->head,sym->word,num);
			printf("  %%%d = bitcast [%d x i32]* %%%s to i8*\n",
					regNum,num,sym->word);
			printf("  call void @llvm.memcpy.p0i8.p0i8.i64(i8* %%%d, i8* bitcast ([%d x i32]* @%s.%s to i8*), i64 8, i32 4, i1 false)\n",
				regNum++,num,funcName,sym->word);
			}
		}
		else // DECEX
		{
			sym->head=(char*)malloc(sizeof(char));
			strcpy(sym->head,"@");
			strcpy(sym->word,id);
			sym->type = 'g';  //global
			printf("%s%s = global [%d x i32] [",
				sym->head,sym->word,num);
			_ARGSINIT(init->son->bro);
			printf("], align 16\n");
		}
	}
}

void _ARGSINIT(struct Node *n)
{
	struct Node *exp = n->son;
	if(n->son->bro==NULL) //EXP
		printf("i32 %d",exp->son->value);
	
	else // EXP COMMA ARGS
	{	
		printf("i32 %d, ",exp->son->value);
		_ARGSINIT(exp->bro->bro);
	}
	
}
void _FUNC(struct Node *n)
{
	regNum = 1;
	tempReg = 0;

	printf("\n; Function Attrs: nounwind uwtable\n");
	printf("define i32 @%s(",n->son->name);
	struct Node *paras = n->son->bro->bro;
	struct Node *pson = paras->son;
	if(pson==NULL) paraFlag = 0;
	else
	{
		paraFlag = 1;
		_PARAS(paras);
	}
	printf(") #0 ");
}

void _PARAS(struct Node *n)
{
	if(n->son==NULL)return;
	if(n->son->bro==NULL)
		_PARA(n->son);
	else
	{
		_PARA(n->son);
		printf(", ");
		_PARAS(n->son->bro->bro);
	}
}

void _PARA(struct Node *n)
{
	struct Node *para = n->son->bro->son;
	
	paraArr[paraNum] = (char*)malloc(sizeof(char)*60);
	strcpy(paraArr[paraNum],para->name);
	paraNum++;
	printf("i32 %%%s",para->name);
}

void _STMTBLOCK(struct Node *n)
{
	if(!BlockLevel)  // for function block
	{
		printf("{\n");
		printf("  %%%d = alloca i32, align 4\n",regNum++);
		int i=0;
		while(paraArr[i])
		{
			printf("  %%%d = alloca i32, align 4\n",regNum);
	printf("  store i32 %%%s, i32* %%%d, align 4    ;store  para \n",
							paraArr[i],regNum);
			char* id = (char*)malloc(sizeof(char)*100);
			strcpy(id,paraArr[i]);
			
			//store the paraments in symTable
			int group;
			group=id[0]-'a';
			if(group<0)group=id[0]-'A';
			if(id[0]=='_')group=26;

			 //find a vacuous space of argument
			int j=0;
			while (symTable[group][j]) j++;	
			symTable[group][j]
                              =(struct symbol*)malloc(sizeof(struct symbol));	
	 		struct symbol *sym=symTable[group][j];
			strcpy(sym->word,id);
			sym->head=(char*)malloc(sizeof(char));
			strcpy(sym->head,"%");
			sym->type = 'a';
			sym->mem = regNum;
			
			regNum++;free(id);
			free(paraArr[i]);paraArr[i]=NULL;
			i++;
		}  	
	}
	
	struct Node *defs=n->son->bro;
	struct Node *stmts=defs->bro;
	_DEFS(defs);
	if(!BlockLevel && paraNum==0)
		printf("  store i32 0, i32* %%1\n");
	paraNum=0;
	_STMTS(stmts);
	
	if(!BlockLevel) printf("}\n");
}

void _STMTS(struct Node *n)
{
	if(n->son==NULL)return;
	_STMT(n->son);
	_STMTS(n->son->bro);
}

void _STMT(struct Node *n)
{
	struct Node *son1=n->son;
	if(son1->bro==NULL)  //STMTBLOCK
	{
		BlockLevel++;
		_STMTBLOCK(son1);
		BlockLevel--;
		return;
	}
	
	if(!strcmp(son1->name,"EXP"))  //EXP SEMI
	{	
		_EXP(son1);
		return;
	}

	if(!strcmp(son1->name,"if"))  //IF LP EXP RP STMT ESTMT
	{
		struct Node *exp=son1->bro->bro;
		struct Node *stmt=exp->bro->bro;
		struct Node *estmt=stmt->bro;
		
		if(!strcmp(exp->son->bro->name,"&&")) // exp => exp && exp
		{
			_IFAND(n);
			return;
		}


		 _EXP(exp);

		if(!strcmp(exp->son->bro->type,"DOT")) // if(st.id)
		{
			printf("  %%%d = icmp ne i32 %%%d, 0\n",
				regNum,regNum-1);
			regNum++;
		}

		// if (x&1)  (x|1)  (x^1)
		if(!strcmp(exp->son->bro->name,"&") ||
		   !strcmp(exp->son->bro->name,"|") ||
		   !strcmp(exp->son->bro->name,"^"))
		{
			printf("  %%%d = icmp ne i32 %%%d, 0\n",
				regNum,regNum-1);
			regNum++;
		}


		if(estmt->son!=NULL)  //with else
		{		
			//DOT CASE not finished

			if(tfFlag==1) //if(1==1)
			{
				_STMT(stmt);
				tfFlag=-1;
				return;
			}
	
			else if(tfFlag==0) //if(1==2)
			{
				_STMT(estmt->son->bro);
				tfFlag=-1;
				return;
			}
	
				
			int labelT=regNum;
			
			printf("  br i1 %%%d, label %%%d",
					regNum-1,labelT);
			long loc1=ftell(ofile); // the loc of %labelF
			
			//first STMT
			regNum++;
			_STMT(stmt);
			int labelF=regNum;
			
			// back to loc1,add the number
			fseek(ofile,loc1,0);
			printf(", label %%%d\n",labelF);

			// repeat STMT
			printf("\n; <label>:%d (T)\n",labelT);
			regNum=labelT+1;
			_STMT(stmt);
			long loc2=ftell(ofile);// the loc of br

			// first ESTMT
			regNum=labelF+1;
			_STMT(estmt->son->bro);
			int after=regNum;

			// back to loc2
			fseek(ofile,loc2,0);
			printf("  br label %%%d\n",after);

			// repeat ESTMT
			printf("\n; <label>:%d (F)\n",labelF);
			regNum=labelF+1;
			_STMT(estmt->son->bro);
			printf("  br label %%%d\n",after);

			// after
			printf("\n; <label>:%d (A)\n",after);
			regNum=after+1;
			
		}

		else   //without else
		{
			int label=regNum;
			
			printf("  br i1 %%%d, label %%%d",
					regNum-1,label);
			long loc=ftell(ofile); // the loc of %label2
			
			//STMT
			regNum++;
			_STMT(stmt);
			int after=regNum;
			
			// back to loc,add the number
			fseek(ofile,loc,0);
			printf(", label %%%d\n",after);

			// repeat STMT
			printf("\n; <label>:%d (T)\n",label);
			regNum=label+1;
			returnFlag=0;
			_STMT(stmt);
			if(returnFlag==0)
				printf("  br label %%%d\n",after);
			returnFlag=0;
			
			// after
			printf("\n; <label>:%d (A)\n",after);
			regNum=after+1;
		}
	}
	
	if(!strcmp(son1->name,"return")) //RETURN EXP SEMI
	{
		returnFlag = 1;
		struct Node *exp=son1->bro;
		if(strcmp(exp->son->name,"0")) //no return 0;
		{
			_EXP(exp);
			printf("  store i32 %%%d, i32* %%1\n",regNum-1);
			printf("  %%%d = load i32* %%1\n",regNum);
			printf("  ret i32 %%%d\n",regNum++);
		}
			
		else
			printf("  ret i32 0\n");//return 0;
	}
	
	if(!strcmp(son1->name,"for")) // FOR LOOP
	{
		struct Node *exp1 = son1->bro->bro;
		struct Node *exp2 = exp1->bro->bro;
		struct Node *exp3 = exp2->bro->bro;
		struct Node *stmt = exp3->bro->bro;

		_FEXP(exp1);

		int start = regNum;
		printf("  br label %%%d\n",start);
		
		printf("\n; <label>:%d (J)\n",start);
		regNum=start+1;
		_FEXP(exp2);
		
		long loc=ftell(ofile);
		int judge=regNum-1;
		int after=regNum;

		// execute the code after for loop
		regNum=after+1;
		_STMTS(n->bro);
		int label=regNum;

		fseek(ofile,loc,0);
		printf("  br i1 %%%d, label %%%d, label %%%d\n",
			judge,label,after);
	
		printf("\n; <label>:%d (A)\n",after);
		regNum=after+1;
		_STMTS(n->bro);
		n->bro->son=NULL; // already exe after,set NULL
		
		printf("\n; <label>:%d (LOOP)\n",label);
		regNum=label+1;
		_STMT(stmt);
		printf("  br label %%%d\n",regNum);

		printf("\n; <label>:%d (C-A)\n",regNum++);
		_FEXP(exp3);
		printf("  br label %%%d\n\n",start);
		
	}
}

void _IFAND(struct Node *n)
{
	struct Node *exp = n->son->bro->bro;
	struct Node *stmt = exp->bro->bro;

	struct Node *exp3 = exp->son->bro->bro;
	struct Node *exp1 = exp->son->son;
	struct Node *exp2 = exp1->bro->bro;
	
	int after;
	
	// to get int after
	_EXP(exp1);
	long loc=ftell(ofile);
	int label=regNum;

	regNum++;
	_EXP(exp2);
	regNum++;
	_EXP(exp3);
	regNum++;
	_STMT(stmt);
	after = regNum;
	
	fseek(ofile,loc,0);
	printf("  br i1 %%%d, label %%%d, label %%%d\n",
			label-1,label,after);
	
	printf("\n; <label>:%d (J2)\n",label);
	regNum = label+1;
	_EXP(exp2);
	printf("  br i1 %%%d, label %%%d, label %%%d\n",
			regNum-1,regNum,after);

	printf("\n; <label>:%d (J3)\n",regNum);
	regNum++;
	_EXP(exp3);
	printf("  br i1 %%%d, label %%%d, label %%%d\n",
			regNum-1,regNum,after);

	printf("\n; <label>:%d (T)\n",regNum);
	regNum++;
	_STMT(stmt);
	printf("  br label %%%d\n",regNum);

	
	printf("\n; <label>:%d (A)\n",regNum);
	regNum++;	
}

void _DEFS(struct Node *n)
{
	
	if(n->son==NULL)return;
	else
	{		
		_DEF(n->son);
		_DEFS(n->son->bro);
	}
}

void _DEF(struct Node *n)
{
	_DECS(n->son->bro);
}

void _DECS(struct Node *n)
{
	struct Node *son1=n->son;
	struct Node *son2=son1->bro;
	if(son2==NULL)
	{
		_DECIN(son1);
	}
	else
	{
		_DECIN(son1);
		_DECS(son2->bro);
	}
}


void _DECIN(struct Node *n)
{
	if(n->son->bro==NULL) //VAR
		_VARNOINIT(n->son);
		
	else//VAR ASSIGNOP INIT
		_VARINIT(n->son);
}


char* _EXP(struct Node *n)
{
	struct Node *son1=n->son;
	if(son1->bro==NULL)	//INT
	{
		char *value = (char*)malloc(sizeof(char)*20);
		sprintf(value,"%d",son1->value);
		return value;
	}

	struct Node *son2=son1->bro;
	
	if(!strcmp(son1->name,"read"))	//read case
	{
		struct Node *exp = son2->bro->son;

		if(!strcmp(exp->son->name,"EXP")) // read struct.ID
		{
		char *st= (char*)malloc(sizeof(char)*100);
		strcpy(st,exp->son->son->name);
		char *id = (char*)malloc(sizeof(char)*100);
		strcpy(id,exp->son->bro->bro->name);

		int group;
		group=id[0]-'a';
		if(group<0)group=id[0]-'A';
		if(id[0]=='_')group=26;
			
		//find the argument
		int i=0;
		while (strcmp(id,symTable[group][i]->word)) i++;
		struct symbol *sym=symTable[group][i];
		
		printf("  %%%d = call i32 (i8*, ...)* @__isoc99_scanf(i8* getelementptr inbounds ([3 x i8]* @.str, i32 0, i32 0), i32* getelementptr inbounds (%%struct.%s* @%s, i32 0, i32 %d))\n",
			regNum++,sym->st,st,sym->stno);
		
		}
	
		else // read ID
		{
		char *id = (char*)malloc(sizeof(char)*100);
		readFlag=1;		
		id = _EXP(exp);
		readFlag=0;
		
		
		printf("  %%%d = call i32 (i8*, ...)* @__isoc99_scanf(i8* getelementptr inbounds ([3 x i8]* @.str, i32 0, i32 0), i32* %s)\n",regNum++,id);
		}	
		return NULL;	
	}
	
	if(!strcmp(son1->name,"write"))	//write case
	{
		char *args = (char*)malloc(sizeof(char)*100);
		struct Node *son3 = son2->bro;
		args = _EXP(son3->son);

		if(!strcmp(son3->son->son->type,"INT"))  //write(int)
			printf("  %%%d = call i32 (i8*, ...)* @printf(i8* getelementptr inbounds ([3 x i8]* @.str, i32 0, i32 0), i32 %s)\n",regNum,_EXP(son3->son));
			
	
		else if(!strcmp(son3->son->son->type,"LBOP")) //write(-int)
			printf("  %%%d = call i32 (i8*, ...)* @printf(i8* getelementptr inbounds ([3 x i8]* @.str, i32 0, i32 0), i32 -%s)\n",regNum,_EXP(son3->son->son->bro));
			

		else
		
			printf("  %%%d = call i32 (i8*, ...)* @printf(i8* getelementptr inbounds ([3 x i8]* @.str, i32 0, i32 0), i32 %%%d)\n",regNum,regNum-1);
			
			
		regNum++;
		return NULL;
	}

	if(!strcmp(son1->type,"ID") && !strcmp(son2->name,"ARRS")) //ID ARRS ...
	{
		if(son2->bro==NULL && son2->son==NULL) //ID (no ARRS)
		{
			char* id = (char*)malloc(sizeof(char)*100);
			strcpy(id,son1->name);
			
			int group;
			group=id[0]-'a';
			if(group<0)group=id[0]-'A';
			if(id[0]=='_')group=26;
			
			//find the argument
			int i=0;
			while (strcmp(id,symTable[group][i]->word)) i++;
			struct symbol *sym=symTable[group][i];

 			sym->reg = regNum;	
			//printf("type:%d\n",sym->type);

			if(!readFlag){
			switch (sym->type)
			{
				case 'a':
			    printf("  %%%d = load i32* %%%d, align 4\n",
                                   regNum++,sym->mem); 
				break;

				case 'l':
			    printf("  %%%d = load i32* %%%s, align 4\n",
			           regNum++,sym->word);
				break;

				case 'g':
			    printf("  %%%d = load i32* @%s, align 4\n",
			           regNum++,sym->word);
				break;

			}}	


			strcpy(id,sym->head);
			strcat(id,sym->word);
			
			return id;
		}

		 // ID (no ARRS) ASSIGNOP EXP
		else if(son2->bro!=NULL && son2->son==NULL)
		{
			struct Node *exp=son2->bro->bro;
			_EXP(exp);

			char* id = (char*)malloc(sizeof(char)*100);
			strcpy(id,son1->name);
			
			int group;
			group=id[0]-'a';
			if(group<0)group=id[0]-'A';
			if(id[0]=='_')group=26;
			
			//find the argument
			int i=0;
			while (strcmp(id,symTable[group][i]->word)) i++;
			struct symbol *sym=symTable[group][i];

 			sym->reg = regNum;
			
			char *OP=son2->bro->name;
			char show[5];
	
			// x = 1;
			if(!strcmp(OP,"=") && !strcmp(exp->son->type,"INT"))
			{
				printf("  store i32 %d, i32* %s%s, align 4\n",
				exp->son->value,sym->head,sym->word);
				return NULL;
			}

			// x = a+b;
			if(!strcmp(OP,"=") && strcmp(exp->son->type,"INT"))
			{
				printf("  store i32 %%%d, i32* %s%s, align 4\n",
				regNum-1,sym->head,sym->word);
				return NULL;
			}

			switch (sym->type)
			{
				case 'a':
			    printf("  %%%d = load i32* %%%d, align 4\n",
                                   regNum++,sym->mem); 
				break;

				case 'l':
			    printf("  %%%d = load i32* %%%s, align 4\n",
			           regNum++,sym->word);
				break;

				case 'g':
			    printf("  %%%d = load i32* @%s, align 4\n",
			           regNum++,sym->word);
				break;

			}

	if(!strcmp(OP,"+="))strcpy(show,"add nsw");
	if(!strcmp(OP,"-="))strcpy(show,"sub nsw");
	if(!strcmp(OP,"*="))strcpy(show,"mul nsw");
	if(!strcmp(OP,"/="))strcpy(show,"sdiv nsw");
	if(!strcmp(OP,"&="))strcpy(show,"and");
	if(!strcmp(OP,"^="))strcpy(show,"xor");
	if(!strcmp(OP,"|="))strcpy(show,"or");
	if(!strcmp(OP,"<<="))strcpy(show,"shl");
	if(!strcmp(OP,">>="))strcpy(show,"ashr");
				
	
			printf("  %%%d = %s i32 %%%d, %d\n",
				regNum,show,regNum-1,exp->son->value);

			printf("  store i32 %%%d, i32* %%2, align 4\n",regNum++);
		}

		else if(son2->bro==NULL && son2->son!=NULL) // ID ARRS case
		{
			char* id = (char*)malloc(sizeof(char)*100);
			strcpy(id,son1->name);
			
			int group;
			group=id[0]-'a';
			if(group<0)group=id[0]-'A';
			if(id[0]=='_')group=26;
			
			//find the argument
			int i=0;
			while (strcmp(id,symTable[group][i]->word)) i++;
			struct symbol *sym=symTable[group][i];

		        struct Node * arrexp = son2->son->bro;

 		  if(!strcmp(arrexp->son->type,"INT"))  // a[1]
		  {	
			switch (sym->type)
			{
				case 'a':
	       printf("  %%%d = getelementptr inbounds [%d x i32]* %%%s, i32 0, i64 %d\n",regNum++,sym->size,sym->word,arrexp->son->value); 
		printf("   %%%d = load i32* %%%d, align 4\n",regNum,regNum-1);
				regNum++;
				break;

				case 'l':
	       printf("  %%%d = getelementptr inbounds [%d x i32]* %%%s, i32 0, i64 %d\n",regNum++,sym->size,sym->word,arrexp->son->value); 
		printf("  %%%d = load i32* %%%d, align 4\n",regNum,regNum-1);
				regNum++;
				break;

				case 'g':
	 printf("  %%%d = load i32* getelementptr inbounds ([%d x i32]* @%s, i32 0, i64 %d), align 4\n",regNum++,sym->size,sym->word,arrexp->son->value);
				break;

			}
		  }

		  else // a[x]
		  {
			_EXP(arrexp);
			printf("  %%%d = sext i32 %%%d to i64\n",
					regNum,regNum-1);
			regNum++;
			printf("  %%%d = getelementptr inbounds [%d x i32]* @%s, i32 0, i64 %%%d\n",regNum,sym->size,sym->word,regNum-1);
			regNum++;
			printf("  %%%d = load i32* %%%d, align 4\n",
					regNum,regNum-1);
			regNum++;
		  }
		}

		else  // ID ARRS ASSIGNOP EXP case
		{
			struct Node *exp=son2->bro->bro;
			_EXP(exp);

			char* id = (char*)malloc(sizeof(char)*100);
			strcpy(id,son1->name);
			
			int group;
			group=id[0]-'a';
			if(group<0)group=id[0]-'A';
			if(id[0]=='_')group=26;
			
			//find the argument
			int i=0;
			while (strcmp(id,symTable[group][i]->word)) i++;
			struct symbol *sym=symTable[group][i];

			struct Node * arrexp = son2->son->bro;

		     if(!strcmp(arrexp->son->type,"INT"))  // a[1] =
		     {
			switch (sym->type)
			{
				case 'a': break;
				
				case 'l': 
			printf("  %%%d = getelementptr inbounds [%d x i32]* %%%s, i32 0, i64 %d\n",regNum++,sym->size,sym->word,arrexp->son->value); 
			printf("  store i32 %%%d, i32* %%%d, align 4\n",
					regNum-2,regNum-1);
				break;

				case 'g':
			printf("  store i32 %%%d, i32* getelementptr inbounds ([%d x i32]* @%s, i32 0, i64 %d), align 4\n",
		regNum-1,sym->size,sym->word,arrexp->son->value); 
				break;
			}
		    }
		
		     else // a[x] = 
		     {
			_EXP(arrexp);
			printf("  %%%d = sext i32 %%%d to i64\n",
					regNum,regNum-1);
			regNum++;
			printf("  %%%d = getelementptr inbounds [%d x i32]* @%s, i32 0, i64 %%%d\n",regNum,sym->size,sym->word,regNum-1);
			regNum++;
			printf("  store i32 %d, i32* %%%d, align 4\n",
				exp->son->value,regNum-1);
		     }
		}
	}

	if(son2->bro!=NULL && !strcmp(son2->bro->name,"EXP")) //EXP BOP EXP
	{
		if((!strcmp(son1->son->type,"INT"))
			&&(!strcmp(son2->bro->son->type,"INT")))
		{
			if(!strcmp(son1->son->name,son2->bro->son->name))
				tfFlag=1;
			else
				tfFlag=0;
			return NULL;
		}
		
		char *op1 = (char*)malloc(sizeof(char)*50);
		op1=_EXP(son1);
		char *op2 = (char*)malloc(sizeof(char)*50);
		op2=_EXP(son2->bro);

		char *OP=son2->name;
		char show[15];

		if(!strcmp(OP,"*"))strcpy(show,"mul nsw");
		if(!strcmp(OP,"/"))strcpy(show,"sdiv");
		if(!strcmp(OP,"%"))strcpy(show,"srem");
		if(!strcmp(OP,"-"))strcpy(show,"sub nsw");
		if(!strcmp(OP,"+"))strcpy(show,"add nsw");
		if(!strcmp(OP,"<<"))strcpy(show,"shl");
		if(!strcmp(OP,">>"))strcpy(show,"ashr");
		if(!strcmp(OP,">"))strcpy(show,"icmp sgt");
		if(!strcmp(OP,">="))strcpy(show,"icmp sge");
		if(!strcmp(OP,"<"))strcpy(show,"icmp slt");
		if(!strcmp(OP,"<="))strcpy(show,"icmp sle");
		if(!strcmp(OP,"=="))strcpy(show,"icmp eq");
		if(!strcmp(OP,"!="))strcpy(show,"icmp ne");
		if(!strcmp(OP,"&"))strcpy(show,"and");
		if(!strcmp(OP,"^"))strcpy(show,"xor");
		if(!strcmp(OP,"|"))strcpy(show,"or");
	

		if(!strcmp(son2->bro->son->type,"INT"))  // eg:x&1
			printf("  %%%d = %s i32 %%%d, %d\n",
			regNum++,show,regNum-1,son2->bro->son->value);

		else if(!strcmp(son1->son->type,"ID"))	// eg:x+y
		{
	printf("  %%%d = %s i32 %%%d, %%%d\n",regNum,show,regNum-2,regNum-1);
		regNum++;
		}

		else if(!strcmp(son1->son->name,"EXP") // eg: st1.x + st2.y
			&& !strcmp(son1->son->bro->type,"DOT"))
		{
	printf("  %%%d = %s i32 %%%d, %%%d\n",regNum,show,regNum-2,regNum-1);
		regNum++;
		}

		else	// eg:a*b+c
		{
	printf("  %%%d = %s i32 %%%s, %%%d\n",regNum,show,op1,regNum-1);
		regNum++;
		}

		tempReg = regNum-1;
		char *re;
		re = (char*)malloc(sizeof(char)*3);
		sprintf(re,"%d",tempReg);
		return re;
	}

	if(!strcmp(son1->type,"LNOT")) // !exp
	{
		char* tmp = _EXP(son2);
		printf("  %%%d = icmp eq i32 %%%d, 0\n",regNum,regNum-1);
		//用eq而不用ne以免需要调换顺序
		regNum++;
	}

	if(!strcmp(son2->name,"("))  // ID (ARGS) -- function( , )
	{
		if(!strcmp(son2->bro->son->son->type,"INT")) // args is int
		{
			printf("  %%%d = call i32 @%s(i32 %d)\n",
				regNum++,son1->name,son2->bro->son->son->value);
			return NULL;
		}

		_ARGSFUNC(son2->bro);
		printf("  %%%d = call i32 @%s(",regNum++,son1->name);
		int i=


		while(paraArr[i])
		{
			if(i>0) printf(", "); 
			char* id = (char*)malloc(sizeof(char)*100);
			strcpy(id,paraArr[i]);
			
			if(id[0]=='*')
			{
				printf("i32 %%%d",tempReg);
				tempReg = 0;
				free(paraArr[i]);paraArr[i]=NULL;
				i++;	
				continue;
			}
			int group;
			group=id[0]-'a';
			if(group<0)group=id[0]-'A';
			if(id[0]=='_')group=26;

			 //find the argument
			int j=0;
			while (strcmp(id,symTable[group][j]->word)) j++;	
	 		struct symbol *sym=symTable[group][j];
			printf("i32 %%%d",sym->reg);
			free(paraArr[i]);paraArr[i]=NULL;
			i++;
		}
		printf(")\n");
		return NULL;
	}
	
	if(!strcmp(son2->type,"DOT"))  // EXP DOT ID ...
	{
		if(son2->bro->bro==NULL) // EXP DOT ID
		{
		char *st= (char*)malloc(sizeof(char)*100);
		strcpy(st,son1->son->name);
		char *id = (char*)malloc(sizeof(char)*100);
		strcpy(id,son2->bro->name);

		int group;
		group=id[0]-'a';
		if(group<0)group=id[0]-'A';
		if(id[0]=='_')group=26;
			
		//find the argument
		int i=0;
		while (strcmp(id,symTable[group][i]->word)) i++;
		struct symbol *sym=symTable[group][i];
		
		printf("  %%%d = load i32* getelementptr inbounds (%%struct.%s* @%s, i32 0, i32 %d), align 4\n",regNum++,sym->st,st,sym->stno);	
		}
	
		else // EXP DOT ID ASSIGNOP EXP
		{
			char *st= (char*)malloc(sizeof(char)*100);
			strcpy(st,son1->son->name);
			char *id = (char*)malloc(sizeof(char)*100);
			strcpy(id,son2->bro->name);

			int group;
			group=id[0]-'a';
			if(group<0)group=id[0]-'A';
			if(id[0]=='_')group=26;
			
			//find the argument
			int i=0;
			while (strcmp(id,symTable[group][i]->word)) i++;
			struct symbol *sym=symTable[group][i];

			struct Node *rexp = son2->bro->bro->bro;
			if(!strcmp(rexp->son->type,"INT"))
			{
			printf("  store i32 %d, i32* getelementptr inbounds (%%struct.%s* @%s, i32 0, i32 %d), align 4\n",
			rexp->son->value,sym->st,st,sym->stno);
			}

			else
			{
			_EXP(rexp->son->bro);
	
			printf("  store i32 %%%d, i32* getelementptr inbounds (%%struct.%s* @%s, i32 0, i32 %d), align 4\n",regNum-1,sym->st,st,sym->stno);
			}
		}
	}

	if(!strcmp(son1->type,"PIN"))  // ++ EXP
	{
		char* id=(char*)malloc(sizeof(char)*100);
		id = _EXP(son1->bro);
		printf("  %%%d = add nsw i32 %%%d, 1\n",regNum,regNum-1);
		printf("  store i32 %%%d, i32* %s, align 4\n",regNum,id);
		regNum++;
	}

	return NULL;	
}


void _FEXP(struct Node *n)
{
	if(n->son==NULL)return;
	
	_EXP(n->son);
	if(n->son->son->bro->bro==NULL)  // if fexp: x
	{
		printf("  %%%d = icmp ne i32 %%%d, 0\n",
			regNum,regNum-1);
				regNum++;
	}	 
}


void _ARGSFUNC(struct Node *n)
{
	if(n->son->bro==NULL) //EXP
	{
		char* args = (char*)malloc(sizeof(char)*100);
		args = _EXP(n->son)+1;
		paraArr[paraNum] = (char*)malloc(sizeof(char)*60);
		if(tempReg) // 参数为计算表达式
			strcpy(paraArr[paraNum],"***");
		else
			strcpy(paraArr[paraNum],args);
		paraNum++;
	}

	else // EXP, ARGS
	{	
		char* args = (char*)malloc(sizeof(char)*100);
		args = _EXP(n->son)+1;
		paraArr[paraNum] = (char*)malloc(sizeof(char)*60);
		if(tempReg) // 参数为计算表达式	
			strcpy(paraArr[paraNum],"***");
		else
			strcpy(paraArr[paraNum],args);
		paraNum++;

		_ARGSFUNC(n->son->bro->bro);
	}
}

