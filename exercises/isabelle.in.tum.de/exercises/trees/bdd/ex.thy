(*
    $Id: ex.thy,v 1.3 2011/06/28 18:11:39 webertj Exp $
    Author: Stefan Berghofer
*)

header {* Binary Decision Diagrams *}

(*<*) theory ex imports Main begin (*>*)

text {*
Boolean functions (in finitely many variables) can be represented by so-called
{\it binary decision diagrams} (BDDs), which are given by the following data
type:
*}

datatype bdd = Leaf bool | Branch bdd bdd

text {*
A constructor @{term "Branch b1 b2"} that is $i$ steps away from the root of
the tree corresponds to a case distinction based on the value of the variable
$v_i$.  If the value of $v_i$ is @{term "False"}, the left subtree @{term "b1"}
is evaluated, otherwise the right subtree @{term "b2"} is evaluated.  The
following figure shows a Boolean function and the corresponding BDD.
\begin{center}
\begin{minipage}{8cm}
\begin{tabular}{|c|c|c|c|} \hline
$v_0$ & $v_1$ & $v_2$ & $f(v_0,v_1,v_2)$ \\ \hline
@{term "False"} & @{term "False"} & *               & @{term "True"} \\
@{term "False"} & @{term "True"}  & *               & @{term "False"} \\
@{term "True"}  & @{term "False"} & *               & @{term "False"} \\
@{term "True"}  & @{term "True"}  & @{term "False"} & @{term "False"} \\
@{term "True"}  & @{term "True"}  & @{term "True"}  & @{term "True"} \\ \hline
\end{tabular}
\end{minipage}
\begin{minipage}{7cm}
\begin{picture}(0,0)%
\includegraphics[scale=0.5]{bdd}%
\end{picture}%
\setlength{\unitlength}{2072sp}%
\begin{picture}(6457,3165)(1329,-4471)
\put(1351,-3571){\makebox(0,0)[b]{@{term "True"}}}%
\put(3151,-3571){\makebox(0,0)[b]{@{term "False"}}}%
\put(4951,-3571){\makebox(0,0)[b]{@{term "False"}}}%
\put(5851,-4471){\makebox(0,0)[b]{@{term "False"}}}%
\put(7651,-4471){\makebox(0,0)[b]{@{term "True"}}}%
\put(7786,-3301){\makebox(0,0)[lb]{$v_2$}}%
\put(7786,-2401){\makebox(0,0)[lb]{$v_1$}}%
\put(7786,-1501){\makebox(0,0)[lb]{$v_0$}}%
\end{picture}
\end{minipage}
\end{center}

{\bf Exercise 1:} Define a function
*}

consts eval :: "(nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> bdd \<Rightarrow> bool"

text {*
that evaluates a BDD under a given variable assignment, beginning at a variable
with a given index.
*}


text {*
{\bf Exercise 2:} Define two functions
*}

consts
  bdd_unop :: "(bool \<Rightarrow> bool) \<Rightarrow> bdd \<Rightarrow> bdd"
  bdd_binop :: "(bool \<Rightarrow> bool \<Rightarrow> bool) \<Rightarrow> bdd \<Rightarrow> bdd \<Rightarrow> bdd"

text {*
for the application of unary and binary operators to BDDs, and prove their
correctness.
*}


text {*
Now use @{term "bdd_unop"} and @{term "bdd_binop"} to define
*}

consts
  bdd_and :: "bdd \<Rightarrow> bdd \<Rightarrow> bdd"
  bdd_or :: "bdd \<Rightarrow> bdd \<Rightarrow> bdd"
  bdd_not :: "bdd \<Rightarrow> bdd"
  bdd_xor :: "bdd \<Rightarrow> bdd \<Rightarrow> bdd"

text {*
and show correctness.
*}


text {*
Finally, define a function
*}

consts bdd_var :: "nat \<Rightarrow> bdd"

text {*
to create a BDD that evaluates to @{term "True"} if and only if the variable
with the given index evaluates to @{term "True"}.  Again prove a suitable
correctness theorem.

{\bf Hint:} If a lemma cannot be proven by induction because in the inductive
step a different value is used for a (non-induction) variable than in the
induction hypothesis, it may be necessary to strengthen the lemma by universal
quantification over that variable (cf.\ Section 3.2 in the Tutorial on
Isabelle/HOL).
*}

text_raw {* \begin{minipage}[t]{0.45\textwidth} *}
 
text{*
{\bf Example:} instead of
*}

lemma "P (b::bdd) x" 
apply (induct b) (*<*) oops (*>*)

text_raw {* \end{minipage} *}
text_raw {* \begin{minipage}[t]{0.45\textwidth} *}   

text {* Strengthening: *}

lemma "\<forall>x. P (b::bdd) x"
apply (induct b) (*<*) oops (*>*)  

text_raw {* \end{minipage} \\[0.5cm]*} 


text {*
{\bf Exercise 3:} Recall the following data type of propositional formulae
(cf.\ the exercise on ``Representation of Propositional Formulae by
Polynomials'')
*}

datatype form = T | Var nat | And form form | Xor form form

text {*
together with the evaluation function @{text "evalf"}:
*}

definition xor :: "bool \<Rightarrow> bool \<Rightarrow> bool" where
  "xor x y \<equiv>  (x \<and> \<not> y) \<or> (\<not> x \<and> y)"

primrec evalf :: "(nat \<Rightarrow> bool) \<Rightarrow> form \<Rightarrow> bool" where
  "evalf e T = True"
| "evalf e (Var i) = e i"
| "evalf e (And f1 f2) = (evalf e f1 \<and> evalf e f2)"
| "evalf e (Xor f1 f2) = xor (evalf e f1) (evalf e f2)"

text {*
Define a function
*}

consts mk_bdd :: "form \<Rightarrow> bdd"

text {*
that transforms a propositional formula of type @{typ "form"} into a BDD.
Prove the correctness theorem
*}

theorem mk_bdd_correct: "eval e 0 (mk_bdd f) = evalf e f"
(*<*) oops (*>*)


(*<*) end (*>*)
