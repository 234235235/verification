
grammar Muds;

@header {
package parser;
}

//NEWLINE : [\r\n]+ ;
PBREAK: 'break';
PABORT: 'abort';
PSTOP: 'stop';
Btrue: 'true';
Bfalse: 'false';
CMP: '==' | '<' | '>' | '>=' | '<=' | '!=' | '<>';
ADDOP: '+' | '-';
MULTOP: '*' | '/';
EPATH: 'E';
APATH: 'A';
NOT: '!';
GLOB: 'G';
EVENT: 'F';
UNTIL: 'U';
NEXT: 'X';
ID : [A-Za-z][A-Za-z0-9_]* ;
INT : [0-9]+ ;
WS : [ \t\r\n]+ -> skip ; // skip spaces, tabs, newlines

// Comment sections, to be dropped (C-style)
BlockComment
    :   '/*' .*? '*/'
        -> skip
    ;
LineComment
    :   '//' ~[\r\n]*
        -> skip
    ;

// Integral expression
iexpr: INT | vname |
    iexpr MULTOP iexpr | // NB: multiplication has precedence, so rule it first !
    iexpr ADDOP iexpr |
    '(' iexpr ')';

// Boolean expression
bexpr: Btrue | Bfalse | vname | NOT bexpr | bexpr '&' bexpr | bexpr '|' bexpr |
    '(' bexpr ')' | iexpr CMP iexpr;

// Expression can be of both type (NB: grammar spec cannot enforce proper typing)
expr: iexpr | bexpr;

// A variable name
vname: ID;

// A variable type (only int and bool are implemented)
type: 'int' | 'bool';

// An action
act: ID | 'tau';

// A prog declaration is a sequence of action and variable declaration followed
// by a process
prog: 'action' ID ';' prog
  | 'int' ID ('=' iexpr)? ';' prog
  | 'bool' ID ('=' bexpr)? ';' prog
  | 'property' ID '=' tform ';' prog
  | process;

process:
	| PSTOP
    | PABORT
    | PBREAK
    | act
    | act '{=' updatelist? '=}'
    | '{' process '}'
	| process ';' process
	| 'alt{' proclist '}'
	| 'do{' proclist '}'
	| 'par{' proclist '}'
    | 'when(' bexpr ')' process
    | 'if(' bexpr ')' process 'else' process
    | 'while(' bexpr ')' process
    | 'do{' process '}'
    ;
//The following is not very useful and will be skipped, at least for the first
//part
//    | 'relabel{' act '}by{' act '}{' process '}'
//    ;
//| processcall;  // Let's not complexify things with process calls
//processcall: 'process' procname '(' paramlist? ')' '{' dcl process '}';
//procname: ID;
//dcl: 'action' ID ';'
//  | type ID ';'
//  | process;
//paramlist: param (',' param)*;
//param: type ID;

proclist: '::' process ('::' process)*;

updatelist: update (',' update)*;

update: vname '=' expr;


// Temporal formulae
tform:  bexpr // case of an atomic proposition
    | tform '&&' tform
    | tform '||' tform
    | '(' tform ')'
    | APATH tform
    | EPATH tform
    | GLOB tform
    | EVENT tform
    | tform UNTIL tform
    | NEXT tform
    | NOT tform
  ;
