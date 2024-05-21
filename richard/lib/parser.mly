%{
open Ast
%}

%token <string> NAME
%token ALL LAM FIX SET SLF INS LBRACE RBRACE LPAREN RPAREN EQ COLON LET DEF HOL VAR EOF

%start main
%type <term> main

%%

main:
  | term EOF { $1 }

term:
  | ALL NAME COLON term RPAREN term { All ($2, $4, fun x -> $6) }
  | LAM NAME term                   { Lam ($2, fun x -> $3) }
  | FIX NAME COLON term RPAREN term { Fix ($2, $4, fun x -> $6) }
  | SET                            { Set }
  | SLF NAME term                   { Slf ($2, fun x -> $3) }
  | INS term                        { Ins ($2) }
  | LBRACE term COLON term RBRACE   { Ann (true, $2, $4) }
  | LET NAME EQ term term           { Let ($2, $4, fun x -> $5) }
  | DEF NAME EQ term term           { Def ($2, $4, fun x -> $5) }
  | HOL NAME                        { Hol ("?" ^ $2, [], []) }
  | VAR NAME                        { Var ($2, 0) }  (* assuming depth is 0 *)
  | NAME                            { Ref $1 }
  | LPAREN term_list RPAREN         { List.fold_left (fun f x -> App (f, x)) (List.hd $2) (List.tl $2) }
  | LPAREN RPAREN                   { raise (Failure "Empty application") }

term_list:
  | term term_list { $1 :: $2 }
  | term           { [$1] }
