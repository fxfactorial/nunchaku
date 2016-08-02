(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Lexer for TPTP} *)

{
  open Nunchaku_core
  open TPTP_parser
}

let printable_char = [^ '\n']
let not_star_slash = ([^ '*']* '*'+ [^ '/' '*'])* [^ '*']*
let comment_line = ['%' '#'] printable_char*
let comment_block = '/' '*' not_star_slash '*' '/'
let comment = comment_line | comment_block

let sq_char = [^ '\\' '''] | "\\\\" | "\\'"
let do_char = [^ '"' '\\' ] |  "\\\\" | "\\\""
let single_quoted = ''' sq_char+ '''
let distinct_object = '"' do_char* '"'

let vline = '|'
let star = '*'
let plus = '+'
let arrow = '>'
let less_sign = '<'

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
let decimal_fraction = decimal dot_decimal
let decimal_exponent = (decimal | decimal_fraction) ['e' 'E'] integer
let unsigned_real = decimal_fraction | decimal_exponent
let signed_real = sign unsigned_real
let real = signed_real | unsigned_real
let unsigned_rational = decimal '/' positive_decimal
let signed_rational = sign unsigned_rational
let rational = signed_rational | unsigned_rational

let lower_alpha = ['a' - 'z']
let upper_alpha = ['A' - 'Z']
let alpha_numeric = lower_alpha | upper_alpha | numeric | '_'

let upper_word = upper_alpha alpha_numeric*
let lower_word = lower_alpha alpha_numeric*
let dollar_word = '$' lower_word
let dollar_dollar_word = "$$" lower_word

rule token = parse
  | comment { token lexbuf }
  | comment_block { token lexbuf }  (* TODO: count new lines in lexeme lexbuf *)
  | '\n' { Lexing.new_line lexbuf; token lexbuf }
  | [' ' '\t' '\r'] { token lexbuf }
  | eof { EOI }
  | "fof" { FOF }
  | "cnf" { CNF }
  | "tff" { TFF }
  | "thf" { THF }
  | "include" { INCLUDE }
  | vline { VLINE }
  | '&' { AND }
  | "!>" { FORALL_TY }
  | "!!" { HO_FORALL }
  | "??" { HO_EXISTS }
  | '^' { LAMBDA }
  | '@' { AT }
  | '!' { FORALL }
  | '?' { EXISTS }
  | "$true" { TRUE }
  | "$false" { FALSE }
  | "$o" { TY_PROP }
  | "$tType" { TY_TYPE }
  | "$_" { WILDCARD }
  (* | ';' { SEMICOLUMN } *)
  | ':' { COLUMN }
  | '>' { ARROW }
  | '*' { STAR }
  | "<=>" { EQUIV }
  | "=>" { IMPLY }
  | "<=" { LEFT_IMPLY }
  | '~' { NOT }
  | "~|" { NOTVLINE }
  | "~&" { NOTAND }
  | '|' { VLINE }
  | "<~>" { XOR }
  | '(' { LEFT_PAREN }
  | ')' { RIGHT_PAREN }
  | '[' { LEFT_BRACKET }
  | ']' { RIGHT_BRACKET }
  | "-->" { GENTZEN_ARROW }
  | '=' { EQUAL }
  | ',' { COMMA }
  | '.' { DOT }
  | '_' { UNDERSCORE }
  | "!=" { NOT_EQUAL }
  | "conjecture" { ROLE_CONJECTURE }
  | "type" { ROLE_TYPE }
  | "axiom" { ROLE_AXIOM }
  | "hypothesis" { ROLE_AXIOM }
  | "definition" { ROLE_DEFINITION }
  | "$ite_f" { ITE_F }
  | "$ite_t" { ITE_T }
  (*
  | "$let_tf" { LET_TF }
  | "$let_tf" { LET_FF }
  *)
  | lower_word { LOWER_WORD(Lexing.lexeme lexbuf) }
  | upper_word { UPPER_WORD(Lexing.lexeme lexbuf) }
  | dollar_word { DOLLAR_WORD(Lexing.lexeme lexbuf) }
  | dollar_dollar_word { DOLLAR_DOLLAR_WORD(Lexing.lexeme lexbuf) }
  | single_quoted { SINGLE_QUOTED(Lexing.lexeme lexbuf) }
  | distinct_object { DISTINCT_OBJECT(Lexing.lexeme lexbuf) }
  | integer { INTEGER(Lexing.lexeme lexbuf) }
  | rational { RATIONAL(Lexing.lexeme lexbuf) }
  | real { REAL(Lexing.lexeme lexbuf) }
  | _ as c
    { Parsing_utils.lex_error_ "lexer fails on char %c" c }


{
  type form = UntypedAST.term

  let parse_str_ p s = p token (Lexing.from_string s)

  let try_parse_ p s =
    try CCResult.return (parse_str_ p s)
    with e -> CCResult.fail (Printexc.to_string e)

  let fo_form_of_string = try_parse_ TPTP_parser.parse_fo_form
  let fo_form_of_string_exn = parse_str_ TPTP_parser.parse_fo_form

  let ho_form_of_string = try_parse_ TPTP_parser.parse_ho_form
  let ho_form_of_string_exn = parse_str_ TPTP_parser.parse_ho_form

  include Parsing_utils.Make(struct
    type token = TPTP_parser.token

    type 'a parser_ = (Lexing.lexbuf -> token) -> Lexing.lexbuf -> 'a

    let token = token
    let parse_ty = TPTP_parser.parse_ty
    let parse_term = TPTP_parser.parse_term
    let parse_statement = TPTP_parser.parse_statement
    let parse_statement_list = TPTP_parser.parse_statement_list
  end)
}
