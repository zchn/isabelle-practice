(*
    $Id: sol.thy,v 1.5 2012/01/04 14:35:44 webertj Exp $
    Author: Farhad Mehta
*)

header {* Recursive Functions and Induction: Zip *}

(*<*) theory sol imports Main begin (*>*)

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

primrec zip1 :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "zip1 []     ys = ys"
| "zip1 (x#xs) ys = (case ys of [] \<Rightarrow> x#xs | z#zs \<Rightarrow> x # z # zip1 xs zs)"

primrec zip2 :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "zip2 xs []     = xs"
| "zip2 xs (y#ys) = (case xs of [] => y#ys | z#zs => z # y # zip2 zs ys)"

fun zipr :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "zipr [] ys = ys"
| "zipr xs [] = xs"
| "zipr (x#xs) (y#ys) = x # y # zipr xs ys"


text {*
Show that all three versions of @{text Zip} are equivalent.
*}

lemma zip1_zip2: "zip1 xs ys = zip2 xs ys"
  apply (induct xs arbitrary: ys)
    apply (case_tac ys)
    apply auto
  apply (case_tac ys)
  apply auto
done

lemma zip2_zipr: "zip2 xs ys = zipr xs ys"
  apply (induct ys arbitrary: xs)
    apply (case_tac xs)
    apply auto
  apply (case_tac xs)
  apply auto
done

lemma "zipr xs ys = zip1 xs ys"
by (simp add: zip1_zip2 zip2_zipr)


text {*
Show that @{text zipr} distributes over @{text append}.
*}

lemma "\<lbrakk>length p = length u; length q = length v\<rbrakk> \<Longrightarrow> 
  zipr (p@q) (u@v) = zipr p u @ zipr q v"
  apply (induct p arbitrary: q u v)
    apply auto
  apply (case_tac u)
    apply auto
done


text {*
{\bf Note:} For @{text fun}, the order of your equations is relevant.
If equations overlap, they will be disambiguated before they are added
to the logic.  You can have a look at these equations using @{text
"thm zipr.simps"}.
*}

(*<*) end (*>*)
