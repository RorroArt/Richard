{
open Parser
}

let whitespace = [' ' '\t' '\r' '\n']
let lowercase = ['a'-'z']
let uppercase = ['A'-'Z']
let digit = ['0'-'9']
let namechar = lowercase | uppercase | digit | '_'

rule tokenize = parse
  | [' ' '\t' '\r' '\n'] { tokenize lexbuf }
  | "//"                 { comment lexbuf }
  | "∀"                  { ALL }
  | "λ"                  { LAM }
  | "μ"                  { FIX }
  | "*"                  { SET }
  | "$"                  { SLF }
  | "~"                  { INS }
  | "{"                  { LBRACE }
  | "}"                  { RBRACE }
  | "("                  { LPAREN }
  | ")"                  { RPAREN }
  | "="                  { EQ }
  | ":"                  { COLON }
  | "let"                { LET }
  | "def"                { DEF }
  | "?"                  { HOL }
  | "%"                  { VAR }
  | namechar+ as name    { NAME name }
  | eof                  { EOF }
  | _                    { raise (Failure "Unexpected character") }

and comment = parse
  | '\n'                 { tokenize lexbuf }
  | _                    { comment lexbuf }
