(*
    $Id: ex.thy,v 1.4 2012/01/04 14:35:44 webertj Exp $
    Author: Farhad Mehta
*)

header {* Recursive Functions and Induction: Zip *}

(*<*) theory ex imports Main begin (*>*)

text {*
Read the chapter about total recursive functions in the ``Tutorial on
Isabelle/HOL'' (@{text fun}, Chapter 3.5).
*}

text {*
In this exercise you will define a function @{text Zip} that merges two lists
by interleaving.
 Examples:
@{text "Zip [a1, a2, a3]  [b1, b2, b3] = [a1, b1, a2, b2, a3, b3]"} 
 and
@{text "Zip [a1] [b1, b2, b3] = [a1, b1, b2, b3]"}.

Use three different approaches to define @{text Zip}:
\begin{enumerate}
\item by primitive recursion on the first list,
\item by primitive recursion on the second list,
\item by total recursion (using @{text fun}).
\end{enumerate}
*}

consts zip1 :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
consts zip2 :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
consts zipr :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"


text {*
Show that all three versions of @{text Zip} are equivalent.
*}


text {*
Show that @{text zipr} distributes over @{text append}.
*}

lemma "\<lbrakk>length p = length u; length q = length v\<rbrakk> \<Longrightarrow> 
  zipr (p@q) (u@v) = zipr p u @ zipr q v"
(*<*) oops (*>*)


text {*
{\bf Note:} For @{text fun}, the order of your equations is relevant.
If equations overlap, they will be disambiguated before they are added
to the logic.  You can have a look at these equations using @{text
"thm zipr.simps"}.
*}

(*<*) end (*>*)
