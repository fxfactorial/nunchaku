
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Lexer for Nunchaku} *)

{

  open Nunchaku_core
  open Parser

}

let printable_char = [^ '\n']
let comment_line = '#' printable_char*

let numeric = ['0' - '9']
let lower_alpha = ['a' - 'z']
let upper_alpha = ['A' - 'Z']
let alpha_numeric = lower_alpha | upper_alpha | numeric | '_'

let upper_word = upper_alpha alpha_numeric*
let lower_word = lower_alpha alpha_numeric*

let filepath = '"' ([^ '"'] | '\\' '"')* '"'

let zero_numeric = '0'
let non_zero_numeric = ['1' - '9']
let numeric = ['0' - '9']
let sign = ['+' '-']

let dot_decimal = '.' numeric +
let positive_decimal = non_zero_numeric numeric*
let decimal = zero_numeric | positive_decimal
let unsigned_integer = decimal
let signed_integer = sign unsigned_integer
let integer = signed_integer | unsigned_integer

rule token = parse
  | eof { EOI }
  | '\n' { Lexing.new_line lexbuf; token lexbuf }
  | [' ' '\t' '\r'] { token lexbuf }
  | comment_line { token lexbuf }
  | '(' { LEFT_PAREN }
  | ')' { RIGHT_PAREN }
  | '[' { LEFT_BRACKET }
  | ']' { RIGHT_BRACKET }
  | '.' { DOT }
  | '_' { WILDCARD }
  | ':' { COLON }
  | ';' { SEMI_COLON }
  | '?' { META_VAR }
  | "=" { LOGIC_EQ }
  | "!=" { LOGIC_NEQ }
  | ":=" { EQDEF }
  | "->" { ARROW }
  | "fun" { FUN }
  | "rec" { REC }
  | "spec" { SPEC }
  | "val" { VAL }
  | "type" { TYPE }
  | "prop" { PROP }
  | "axiom" { AXIOM }
  | "goal" { GOAL }
  | "match" { MATCH }
  | "with" { WITH }
  | "end" { END }
  | "let" { LET }
  | "in" { IN }
  | "if" { IF }
  | "then" { THEN }
  | "else" { ELSE }
  | "asserting" { ASSERTING }
  | "and" { AND }
  | "true" { LOGIC_TRUE }
  | "false" { LOGIC_FALSE }
  | "pi" { PI }
  | "data" { DATA }
  | "codata" { CODATA }
  | "pred" { PRED }
  | "copred" { COPRED }
  | "include" { INCLUDE }
  | "copy" { COPY }
  | "subset" { SUBSET }
  | "quotient" { QUOTIENT }
  | "partial_quotient" { PARTIAL_QUOTIENT }
  | "abstract" { ABSTRACT }
  | "concrete" { CONCRETE }
  | "wf" { WF_ATTRIBUTE }
  | "&&" { LOGIC_AND }
  | "||" { LOGIC_OR }
  | "|" { VERTICAL_BAR }
  | '~' { LOGIC_NOT }
  | "forall" { LOGIC_FORALL }
  | "exists" { LOGIC_EXISTS }
  | "=>" { LOGIC_IMPLY }
  | '@' { AT }
  | lower_word { LOWER_WORD(Lexing.lexeme lexbuf) }
  | upper_word { UPPER_WORD(Lexing.lexeme lexbuf) }
  | integer { INTEGER(Lexing.lexeme lexbuf) }
  | filepath {
      let s = Lexing.lexeme lexbuf in
      let s = String.sub s 1 (String.length s -2) in (* remove " " *)
      FILEPATH s }
  | _ as c
    {
      let loc = Location.of_lexbuf lexbuf in
      Parsing_utils.lex_error_ ~loc "unexpected char '%c'" c
    }

{
  include Parsing_utils.Make(struct
    type token = Parser.token

    type 'a parser_ = (Lexing.lexbuf -> token) -> Lexing.lexbuf -> 'a

    let token = token
    let parse_ty = Parser.parse_ty
    let parse_term = Parser.parse_term
    let parse_statement = Parser.parse_statement
    let parse_statement_list = Parser.parse_statement_list
  end)

}
