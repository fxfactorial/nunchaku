
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Flatten pattern-matching in Equations}

  Transform an equation
  [forall x y. f (x :: y) = rhs]
  into
  [forall l. is_cons l => f l = rhs(x:=select_cons_1 l, y:=select_cons_2 l)]

  Namely, it changes an equations with a pattern on the left, into an equation
  with a linear irrefutable pattern on the left; in other words, the result
  has the form
  [forall x1...xn, f x1...xn = rhs]

  Another example:
  [f (s 0) = rhs]
  becomes
  [forall l. is_s l && is_0 (select_s_1 l) ==> f l = rhs]

  A non-algebraic type could be encoded using an existential:

  [forall x. f (g x) = rhs]
  might become
  [forall y. (exists x. y = g x => f y = rhs[x := ??]

  but we lack some choice operator
*)

type id = NunID.t

exception Error of string

type inv = <poly:[`Mono]; meta:[`NoMeta]>

module Make(T : NunTerm_ho.S) : sig
  type term = inv T.t
  type env = (term, term, [`Linear]) NunEnv.t

  val tr_statement :
    env:env ->
    (term, term, [`Nested]) NunStatement.t ->
    env * (term, term, [`Linear]) NunStatement.t
  (** Flatten a single equation, using inductive selectors/discriminators
      and existential variables for eliminating the left-hand side pattern.
      Preserves other statements identically.
      @param env the current environment
      @raise Error if the equation LHS is not a proper pattern *)

  val tr_problem:
    (term, term, [`Nested]) NunProblem.t ->
    (term, term, [`Linear]) NunProblem.t

  val pipe :
    print:bool ->
      ((term, term, [`Nested]) NunProblem.t,
      (term, term, [`Linear]) NunProblem.t,
      'b, 'b
    ) NunTransform.t
  (** Pipeline component. Reverse direction is identity. *)
end