(*
    $Id: ex.thy,v 1.3 2008/07/04 15:37:41 nipkow Exp $
    Author: Stefan Berghofer, Tobias Nipkow
*)

header {* Representation of Propositional Formulae by Polynomials *}

(*<*) theory ex imports Main begin (*>*)

text {*
Let the following data type for propositional formulae be given:
*}

datatype form = T | Var nat | And form form | Xor form form

text {*
Here @{term "T"} denotes a formula that is always true, @{term "Var n"} denotes
a propositional variable, its name given by a natural number, @{term "And f1
f2"} denotes the AND combination, and @{term "Xor f1 f2"} the XOR (exclusive or)
combination of two formulae.  A constructor @{term "F"} for a formula that is
always false is not necessary, since @{term "F"} can be expressed by @{term "Xor
T T"}.

{\bf Exercise 1:} Define a function
*}

(*<*)consts(*>*)  evalf :: "(nat \<Rightarrow> bool) \<Rightarrow> form \<Rightarrow> bool"

text {*
that evaluates a formula under a given variable assignment.
*}


text {*
Propositional formulae can be represented by so-called {\it polynomials}.  A
polynomial is a list of lists of propositional variables, i.e.\ an element of
type @{typ "nat list list"}.  The inner lists (the so-called {\it monomials})
are interpreted as conjunctive combination of variables, whereas the outer list
is interpreted as exclusive-or combination of the inner lists.

{\bf Exercise 2:} Define two functions
*}

(*<*)consts(*>*)
  evalm :: "(nat \<Rightarrow> bool) \<Rightarrow> nat list \<Rightarrow> bool"
  evalp :: "(nat \<Rightarrow> bool) \<Rightarrow> nat list list \<Rightarrow> bool"

text {*
for evaluation of monomials and polynomials under a given variable assignment.
In particular think about how empty lists have to be evaluated.
*}


text {*
{\bf Exercise 3:} Define a function
*}

(*<*)consts(*>*)  poly :: "form \<Rightarrow> nat list list"

text {*
that turns a formula into a polynomial.  You will need an auxiliary function
*}

(*<*)consts(*>*)  mulpp :: "nat list list \<Rightarrow> nat list list \<Rightarrow> nat list list"

text {*
to ``multiply'' two polynomials, i.e.\ to compute
\[
((v^1_1 \mathbin{\odot} \cdots \mathbin{\odot} v^1_{m_1}) \mathbin{\oplus} \cdots \mathbin{\oplus} (v^k_1 \mathbin{\odot} \cdots \mathbin{\odot} v^k_{m_k})) \mathbin{\odot}
((w^1_1 \mathbin{\odot} \cdots \mathbin{\odot} w^1_{n_1}) \mathbin{\oplus} \cdots \mathbin{\oplus} (w^l_1 \mathbin{\odot} \cdots \mathbin{\odot} w^l_{n_l}))
\]
where $\mathbin{\oplus}$ denotes ``exclusive or'', and $\mathbin{\odot}$ denotes
``and''.  This is done using the usual calculation rules for addition and
multiplication.
*}


text {*
{\bf Exercise 4:} Now show correctness of your function @{term "poly"}:
*}

theorem poly_correct: "evalf e f = evalp e (poly f)"
(*<*) oops (*>*)

text {*
It is useful to prove a similar correctness theorem for @{term "mulpp"} first.
*}


(*<*) end (*>*)
