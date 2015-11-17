
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Lexer for Nunchaku} *)

{

  open NunParser

}

let printable_char = [^ '\n']
let comment_line = '#' printable_char*

let numeric = ['0' - '9']
let lower_alpha = ['a' - 'z']
let upper_alpha = ['A' - 'Z']
let alpha_numeric = lower_alpha | upper_alpha | numeric | '_'

let upper_word = upper_alpha alpha_numeric*
let lower_word = lower_alpha alpha_numeric*

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
  | '.' { DOT }
  | '_' { WILDCARD }
  | ':' { COLON }
  | ';' { SEMI_COLON }
  | '?' { META_VAR }
  | "=" { LOGIC_EQ }
  | ":=" { EQDEF }
  | "->" { ARROW }
  | "as" { AS }
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
  | "and" { AND }
  | "true" { LOGIC_TRUE }
  | "false" { LOGIC_FALSE }
  | "pi" { PI }
  | "data" { DATA }
  | "codata" { CODATA }
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
  | _ as c
    {
      NunParsingUtils.lex_error_ "lexer fails on char '%c'" c
    }

{
  include NunParsingUtils.Make(struct
    type token = NunParser.token

    type 'a parser_ = (Lexing.lexbuf -> token) -> Lexing.lexbuf -> 'a

    let token = token
    let parse_ty = NunParser.parse_ty
    let parse_term = NunParser.parse_term
    let parse_statement = NunParser.parse_statement
    let parse_statement_list = NunParser.parse_statement_list
  end)

}
