(*
    $Id: sol.thy,v 1.3 2011/06/28 18:11:39 webertj Exp $
    Author: Stefan Berghofer
*)

header {* Binary Decision Diagrams *}

(*<*) theory sol imports Main begin (*>*)

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

  @{text "eval :: (nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> bdd \<Rightarrow> bool"}

that evaluates a BDD under a given variable assignment, beginning at a variable
with a given index.
*}

primrec eval :: "(nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> bdd \<Rightarrow> bool" where
  "eval e i (Leaf x) = x"
| "eval e i (Branch b1 b2) =
     (if e i then eval e (Suc i) b2 else eval e (Suc i) b1)"


text {*
{\bf Exercise 2:} Define two functions

  @{text "bdd_unop :: (bool \<Rightarrow> bool) \<Rightarrow> bdd \<Rightarrow> bdd"}\\
  @{text "bdd_binop :: (bool \<Rightarrow> bool \<Rightarrow> bool) \<Rightarrow> bdd \<Rightarrow> bdd \<Rightarrow> bdd"}

for the application of unary and binary operators to BDDs, and prove their
correctness.
*}

primrec bdd_unop :: "(bool \<Rightarrow> bool) \<Rightarrow> bdd \<Rightarrow> bdd" where
  "bdd_unop f (Leaf x) = Leaf (f x)"
| "bdd_unop f (Branch b1 b2) = Branch (bdd_unop f b1) (bdd_unop f b2)"

primrec bdd_binop :: "(bool \<Rightarrow> bool \<Rightarrow> bool) \<Rightarrow> bdd \<Rightarrow> bdd \<Rightarrow> bdd" where
  "bdd_binop f (Leaf x) b = bdd_unop (f x) b"
| "bdd_binop f (Branch b1 b2) b = (case b of
       Leaf x \<Rightarrow> Branch (bdd_binop f b1 (Leaf x)) (bdd_binop f b2 (Leaf x))
     | Branch b1' b2' \<Rightarrow> Branch (bdd_binop f b1 b1') (bdd_binop f b2 b2'))"

theorem bdd_unop_correct:
  "\<forall>i. eval e i (bdd_unop f b) = f (eval e i b)"
  apply (induct b)
  apply auto
done 

theorem bdd_binop_correct:
  "\<forall>i b2. eval e i (bdd_binop f b1 b2) = f (eval e i b1) (eval e i b2)"
  apply (induct b1)
  apply (auto simp add: bdd_unop_correct)
  apply (case_tac b2)
  apply auto
  apply (case_tac b2)
  apply auto
  apply (case_tac b2)
  apply auto
  apply (case_tac b2)
  apply auto
done 


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

defs
  bdd_and_def: "bdd_and \<equiv> bdd_binop op \<and>"
  bdd_or_def: "bdd_or \<equiv> bdd_binop op \<or>"
  bdd_not_def: "bdd_not \<equiv> bdd_unop Not"
  bdd_xor_def: "bdd_xor b1 b2 == (bdd_or
     (bdd_and (bdd_not b1) b2) (bdd_and b1 (bdd_not b2)))"

theorem bdd_and_correct:
  "eval e i (bdd_and b1 b2) = (eval e i b1 \<and> eval e i b2)"
  apply (auto simp add: bdd_and_def bdd_binop_correct)
done

theorem bdd_or_correct:
  "eval e i (bdd_or b1 b2) = (eval e i b1 \<or> eval e i b2)"
  apply (auto simp add: bdd_or_def bdd_binop_correct)
done

theorem bdd_not_correct: "eval e i (bdd_not b) = (\<not> eval e i b)"
  apply (auto simp add: bdd_not_def bdd_unop_correct)
done


text {*
Finally, define a function

  @{text "bdd_var :: nat \<Rightarrow> bdd"}

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

primrec bdd_var :: "nat \<Rightarrow> bdd" where
  "bdd_var 0 = Branch (Leaf False) (Leaf True)"
| "bdd_var (Suc i) = Branch (bdd_var i) (bdd_var i)"

theorem bdd_var_correct: "\<forall>j. eval e j (bdd_var i) = e (i+j)"
  apply (induct i)
  apply auto
done


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

  @{text "mk_bdd :: form \<Rightarrow> bdd"}

that transforms a propositional formula of type @{typ "form"} into a BDD.
Prove the correctness theorem
*}

theorem mk_bdd_correct: "eval e 0 (mk_bdd f) = evalf e f"
(*<*) oops (*>*)

primrec mk_bdd :: "form \<Rightarrow> bdd" where
  "mk_bdd T = Leaf True"
| "mk_bdd (Var i) = bdd_var i"
| "mk_bdd (And f1 f2) = bdd_and (mk_bdd f1) (mk_bdd f2)"
| "mk_bdd (Xor f1 f2) = bdd_xor (mk_bdd f1) (mk_bdd f2)"

theorem mk_bdd_correct: "eval e 0 (mk_bdd f) = evalf e f"
  apply (induct f)
  apply (auto simp add: bdd_var_correct
    bdd_and_correct bdd_or_correct bdd_not_correct bdd_xor_def xor_def)
done


(*<*) end (*>*)
