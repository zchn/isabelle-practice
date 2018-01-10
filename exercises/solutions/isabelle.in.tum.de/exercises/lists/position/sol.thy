(*
    $Id: sol.thy,v 1.3 2011/06/28 18:11:37 webertj Exp $
    Author: Martin Strecker
*)

header {* Searching in Lists *}

(*<*) theory sol imports Main begin (*>*)

text {* Define a function @{text first_pos} that computes the index
of the first element in a list that satisfies a given predicate:

  @{text "first_pos :: ('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> nat"}

The smallest index is @{text 0}.  If no element in the
list satisfies the predicate, the behaviour of @{text first_pos} should
be as described below. *}

primrec first_pos :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> nat" where
  "first_pos P [] = 0"
| "first_pos P (x # xs) = (if P x then 0 else Suc (first_pos P xs))"


text {* Verify your definition by computing
\begin{itemize}
\item the index of the first number equal to @{text 3} in the list
  @{text "[1::nat, 3, 5, 3, 1]"},
\item the index of the first number greater than @{text 4} in the list
  @{text "[1::nat, 3, 5, 7]"},
\item the index of  the first list with more than one element in the list
  @{text "[[], [1, 2], [3]]"}.
\end{itemize}

\emph{Note:} Isabelle does not know the operators @{text ">"} and @{text
"\<ge>"}.  Use @{text "<"} and @{text "\<le>"} instead. *}

lemma "first_pos (\<lambda> x. x = 3) [1::nat, 3, 5, 3, 1] = 1"
  by auto

lemma "first_pos (\<lambda> x. 4 < x) [1::nat, 3, 5, 7] = 2"
  by auto

lemma "first_pos (\<lambda> x. 1 < length x) [[], [1, 2], [3]] = 1"
  by auto


text {* Prove that @{text first_pos} returns the length of the list if
and only if no element in the list satisfies the given predicate. *}

lemma "list_all (\<lambda> x. \<not> P x) xs = (first_pos P xs = length xs)"
  apply (induct xs)
  apply auto
done


text {* Now prove: *}

lemma "list_all (\<lambda> x. \<not> P x) (take (first_pos P xs) xs)"
  apply (induct xs)
  apply auto
done


text {* How can @{text "first_pos (\<lambda> x. P x \<or> Q x) xs"} be computed from
@{text "first_pos P xs"} and @{text "first_pos Q xs"}?  Can something
similar be said for the conjunction of @{text P} and @{text Q}?  Prove
your statement(s). *}

lemma "first_pos (\<lambda> x. P x \<or> Q x) xs = min (first_pos P xs) (first_pos Q xs)"
  apply (induct xs)
  apply auto
done

text {* For @{text "\<and>"}, only a lower bound can be given. *}

lemma "max (first_pos P xs) (first_pos Q xs) \<le> first_pos (\<lambda> x. P x \<and> Q x) xs"
  apply (induct xs)
  apply auto
done


text {* Suppose @{text P} implies @{text Q}. What can be said about the
relation between @{text "first_pos P xs"} and @{text "first_pos Q xs"}?
Prove your statement. *}

lemma "(\<forall>x. P x \<longrightarrow> Q x) \<longrightarrow> first_pos Q xs \<le> first_pos P xs"
  apply (induct xs)
  apply auto
done


text {* Define a function @{text count} that counts the number of
elements in a list that satisfy a given predicate. *}

primrec count :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> nat" where
  "count P [] = 0"
| "count P (x # xs) = (if P x then Suc (count P xs) else (count P xs))"


text {* Show: The number of elements with a given property stays the
same when one reverses a list with @{text rev}.  The proof will require
a lemma. *}

lemma count_append[simp]: "count P (xs @ ys) = count P xs + count P ys"
  apply (induct xs)
  apply auto
done

lemma "count P xs = count P (rev xs)"
  apply (induct xs)
  apply auto
done


text {* Find and prove a connection between the two functions @{text filter}
and @{text count}. *}

lemma "length (filter P xs) = count P xs"
  apply (induct xs)
  apply auto
done


(*<*) end (*>*)
