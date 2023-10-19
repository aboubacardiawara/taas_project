%left PLUS MINUS
%left TIMES
%nonassoc UMINUS
%type <unit> main expression
%start main
%%
main:
expression EOL
{}
;

expression:
expression PLUS expression
{}
| expression MINUS expression
{}
| expression TIMES expression
{}
| GPAREN expression DPAREN
{}
| MINUS expression %prec UMINUS
{}
| NUMBER
{}
;