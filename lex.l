%{
 	/*Project of Computer Principles.
          Created by Zheng Linghan,5130309485.
        
          This first section contains necessary 
     	  C delarations and includes
     	  to use throughout the lex specifications.*/
	#include <stdio.h>
	#include <stdlib.h>
	#include <assert.h>
	#include <string.h>

	#include "y.tab.h"

	extern void yyerror(char *s);

	int line=0;
	
	struct Node
	{
		char name[100];
		char type[10];
		int line;
		int value;
		struct Node *son;
		struct Node *bro;
	};

	struct Node* setNode(char *n,char *t,int l)
	{
		struct Node *p=(struct de*)malloc(sizeof(struct Node));
		strcpy(p->name,n);
		strcpy(p->type,t);
		p->line=l;
		if(!strcmp(t,INT'))p->value=getValue(p->name);
		p->son=NULL;
		p->bro=NULL;
		return p;
	}

	int getValue(char *txt)
	{
		int value=0;
		int l=strlen(txt);
		int i;
		if(txt[0]!='0')  /*dec*/
		{
			for(i=0;i<l;++i)
				value=(txt[i]-'0')+value*10;
				
		}
		
		else if(txt[1]=='x'||txt[1]=='X') /*hex*/
		{
			
			for(i=2;i<l;++i)
			{
				if(txt[i]>='A'&& txt[i]<='F')
					value=(txt[i]-'7')+value*16;
				else
					value=(txt[i]-'0')+value*16;

			}

		else /*oct*/
		{
			for(i=1;i<l;++i)
				value=(txt[i]-'0')+value*8;
		}

		return value;
	}
%}

/*regular definitions*/
delim	[ \t]
ws	{delim}+
letter	[A-Za-z]
digit	[0-9]
id	{letter}({letter}|{digit})*
int	0?(x|X)?(([0-7]+)|([0-9A-F]+))

%%

{ws}		/*no action*/
\n		{line++;}

if		{yylval.node=setNode(yytext,"IF",line);return(IF);}
then		{yylval.node=seteNode(yytext,"THEN",line);return(THEN);}
else		{yylval.node=setNode(yytext,"ELSE",line);return(ELSE);}
struct		{yylval.node=setNode(yytext,"STRUCT",line);return(STRUCT);}
return		{yylval.node=setNode(yytext,"RETURN",line);return(RETURN);}
break		{yylval.node=setNode(yytext,"BREAK",line);return(BREAK);}
continue	{yylval.node=setNode(yytext,"CONT",line);return(CONT);}
for		{yylval.node=setNode(yytext,"FOR",line);return(FOR);}
int    	 	{yylval.node=setNode(yytext,"TYPE",line);return(TYPE);}

{id}		{yylval.node=setNode(yytext,"ID",line);return(ID);}
{int} 		{yylval.node=setNode(yytext,"INT",line);return(INT);}

","		{yylval.node=setNode(yytext,"COMMA",line);return(COMMA);}
"."		{yylval.node=setNode(yytext,"DOT",line);return(DOT);}
";"		{yylval.node=setNode(yytext,"SEMI",line);return(SEMI);}

"("		{yylval.node=setNode(yytext,"BRACKET",line);return(LP);}
")"		{yylval.node=setNode(yytext,"BRACKET",line);return(RP);}
"["		{yylval.node=setNode(yytext,"BRACKET",line);return(LB);}
"]"	{yylval.node=setNode(yytext,"BRACKET",line);return(RB);}		
"{"		{yylval.node=setNode(yytext,"BRACKET",line);return(LC);}
"}"		{yylval.node=setNode(yytext,"BRACKET",line);return(RC);}

"!"		{yylval.node=setNode(yytext,"LNOT",line);return(LNOT);}
"++"		{yylval.node=setNode(yytext,"PIN",line);return(PIN);}
"--"		{yylval.node=setNode(yytext,"PDE",line);return(PDE);}
"~"		{yylval.node=setNode(yytext,"BNOT",line);return(BNOT);}

[*/%]		{yylval.node=setNode(yytext,"HBOP",line);return(HBOP);}
[-+]		{yylval.node=setNode(yytext,"LBOP",line);return(LBOP);}

"<<"		{yylval.node=setNode(yytext,"SHIFT",line);return(SHIFT);}
">>"		{yylval.node=setNode(yytext,"SHIFT",line);return(SHIFT);}

">"		{yylval.node=setNode(yytext,"COMP",line);return(COMP);}
">="		{yylval.node=setNode(yytext,"COMP",line);return(COMP);}
"<"		{yylval.node=setNode(yytext,"COMP",line);return(COMP);}
"<="		{yylval.node=setNode(yytext,"COMP",line);return(COMP);}

"=="		{yylval.node=setNode(yytext,"EQU",line);return(EQU);}
"!="		{yylval.node=setNode(yytext,"NE",line);return(NE);}

"&"		{yylval.node=setNode(yytext,"BAND",line);return(BAND);}
"^"		{yylval.node=setNode(yytext,"BXOR",line);return(BXOR);}
"|"		{yylval.node=setNode(yytext,"BOR",line);return(BOR);}
"&&"		{yylval.node=setNode(yytext,"LAND",line);return(LAND);}
"||"		{yylval.node=setNode(yytext,"LOR",line);return(LOR);}

"="		{yylval.node=setNode(yytext,"ASSIGNOP",line);return(ASSIGNOP);}
"+="		{yylval.node=setNode(yytext,"ASSIGNOP",line);return(ASSIGNOP);}
"-="		{yylval.node=setNode(yytext,"ASSIGNOP",line);return(ASSIGNOP);}
"*="		{yylval.node=setNode(yytext,"ASSIGNOP",line);return(ASSIGNOP);}
"/="		{yylval.node=setNode(yytext,"ASSIGNOP",line);return(ASSIGNOP);}
"&="		{yylval.node=setNode(yytext,"ASSIGNOP",line);return(ASSIGNOP);}
"^="		{yylval.node=setNode(yytext,"ASSIGNOP",line);return(ASSIGNOP);}
"|="		{yylval.node=setNode(yytext,"ASSIGNOP",line);return(ASSIGNOP);}
"<<="		{yylval.node=setNode(yytext,"ASSIGNOP",line);return(ASSIGNOP);}
">>="		{yylval.node=setNode(yytext,"ASSIGNOP",line);return(ASSIGNOP);}

.               yyerror("Lexical Error.");

%%
int yywrap(void)
{
	return 1;
}
