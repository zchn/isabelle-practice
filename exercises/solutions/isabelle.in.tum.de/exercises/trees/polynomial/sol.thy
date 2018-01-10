(*
    $Id: sol.thy,v 1.3 2011/06/28 18:11:39 webertj Exp $
    Author: Stefan Berghofer, Tobias Nipkow
*)

header {* Representation of Propositional Formulae by Polynomials *}

(*<*) theory sol imports Main begin (*>*)

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

  @{term "evalf :: (nat \<Rightarrow> bool) \<Rightarrow> form \<Rightarrow> bool"}

that evaluates a formula under a given variable assignment.
*}

definition
  xor :: "bool \<Rightarrow> bool \<Rightarrow> bool" where
  "xor x y \<equiv>  (x \<and> \<not> y) \<or> (\<not> x \<and> y)"

primrec evalf :: "(nat \<Rightarrow> bool) \<Rightarrow> form \<Rightarrow> bool" where
  "evalf e T = True"
| "evalf e (Var i) = e i"
| "evalf e (And f1 f2) = (evalf e f1 \<and> evalf e f2)"
| "evalf e (Xor f1 f2) = xor (evalf e f1) (evalf e f2)"


text {*
Propositional formulae can be represented by so-called {\it polynomials}.  A
polynomial is a list of lists of propositional variables, i.e.\ an element of
type @{typ "nat list list"}.  The inner lists (the so-called {\it monomials})
are interpreted as conjunctive combination of variables, whereas the outer list
is interpreted as exclusive-or combination of the inner lists.

{\bf Exercise 2:} Define two functions

  @{text "evalm :: (nat \<Rightarrow> bool) \<Rightarrow> nat list \<Rightarrow> bool"}\\
  @{text "evalp :: (nat \<Rightarrow> bool) \<Rightarrow> nat list list \<Rightarrow> bool"}

for evaluation of monomials and polynomials under a given variable assignment.
In particular think about how empty lists have to be evaluated.
*}

primrec evalm :: "(nat \<Rightarrow> bool) \<Rightarrow> nat list \<Rightarrow> bool" where
  "evalm e [] = True"
| "evalm e (x # xs) = (e x \<and> evalm e xs)"

primrec evalp :: "(nat \<Rightarrow> bool) \<Rightarrow> nat list list \<Rightarrow> bool" where
  "evalp e [] = False"
| "evalp e (m # p) = xor (evalm e m) (evalp e p)"


text {*
{\bf Exercise 3:} Define a function

  @{text "poly :: form \<Rightarrow> nat list list"}

that turns a formula into a polynomial.  You will need an auxiliary function

  @{text "mulpp :: nat list list \<Rightarrow> nat list list \<Rightarrow> nat list list"}

to ``multiply'' two polynomials, i.e.\ to compute
\[
((v^1_1 \mathbin{\odot} \cdots \mathbin{\odot} v^1_{m_1}) \mathbin{\oplus} \cdots \mathbin{\oplus} (v^k_1 \mathbin{\odot} \cdots \mathbin{\odot} v^k_{m_k})) \mathbin{\odot}
((w^1_1 \mathbin{\odot} \cdots \mathbin{\odot} w^1_{n_1}) \mathbin{\oplus} \cdots \mathbin{\oplus} (w^l_1 \mathbin{\odot} \cdots \mathbin{\odot} w^l_{n_l}))
\]
where $\mathbin{\oplus}$ denotes ``exclusive or'', and $\mathbin{\odot}$ denotes
``and''.  This is done using the usual calculation rules for addition and
multiplication.
*}

primrec mulpp :: "nat list list \<Rightarrow> nat list list \<Rightarrow> nat list list" where
  "mulpp [] q = []"
| "mulpp (m # p) q = map (op @ m) q @ (mulpp p q)"

primrec poly :: "form \<Rightarrow> nat list list" where
  "poly T = [[]]"
| "poly (Var i) = [[i]]"
| "poly (Xor f1 f2) = poly f1 @ poly f2"
| "poly (And f1 f2) = mulpp (poly f1) (poly f2)"


text {*
{\bf Exercise 4:} Now show correctness of your function @{term "poly"}:
*}

theorem poly_correct: "evalf e f = evalp e (poly f)"
(*<*) oops (*>*)

text {*
It is useful to prove a similar correctness theorem for @{term "mulpp"} first.
*}

lemma evalm_app: "evalm e (xs @ ys) = (evalm e xs \<and> evalm e ys)"
  apply (induct xs)
  apply auto
done

lemma evalp_app: "evalp e (xs @ ys) = (xor (evalp e xs) (evalp e ys))"
  apply (induct xs)
  apply (auto simp add: xor_def)
done

theorem mulmp_correct: "evalp e (map (op @ m) p) = (evalm e m \<and> evalp e p)"
  apply (induct p)
  apply (auto simp add: xor_def evalm_app)
done

theorem mulpp_correct: "evalp e (mulpp p q) = (evalp e p \<and> evalp e q)"
  apply (induct p)
  apply (auto simp add: xor_def mulmp_correct evalp_app)
done

theorem poly_correct: "evalf e f = evalp e (poly f)"
  apply (induct f)
  apply (auto simp add: xor_def mulpp_correct evalp_app)
done


(*<*) end (*>*)
