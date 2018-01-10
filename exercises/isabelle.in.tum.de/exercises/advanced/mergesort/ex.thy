(*
    $Id: ex.thy,v 1.2 2004/11/23 15:14:34 webertj Exp $
    Author: Gerwin Klein
*)

header {* Merge Sort *}

(*<*) theory ex imports Main begin (*>*)

subsection {* Sorting with lists *}

text {*
  For simplicity we sort natural numbers.

  Define a predicate @{term sorted} that checks if each element in the list is
  less or equal to the following ones; @{term "le n xs"} should be true iff
  @{term n} is less or equal to all elements of @{text xs}.
*}

consts 
  le     :: "nat \<Rightarrow> nat list \<Rightarrow> bool"
  sorted :: "nat list \<Rightarrow> bool"


text {*
  Define a function @{term "count xs x"} that counts how often @{term x} occurs
  in @{term xs}.
*}

consts
  count :: "nat list => nat => nat"


subsection {* Merge sort *}

text {*
  Implement \emph{merge sort}: a list is sorted by splitting it into two lists,
  sorting them separately, and merging the results.

  With the help of @{text recdef} define two functions
*}

consts merge :: "nat list \<times> nat list \<Rightarrow> nat list"
       msort :: "nat list \<Rightarrow> nat list"


text {* and show *}

theorem "sorted (msort xs)"
(*<*)oops(*>*)

theorem "count (msort xs) x = count xs x"
(*<*)oops(*>*)


text {*
  You may have to prove lemmas about @{term sorted} and @{term count}.

  Hints:
  \begin{itemize}
  \item For @{text recdef} see Section~3.5 of the Isabelle/HOL tutorial.

  \item To split a list into two halves of almost equal length you can use the
  functions \mbox{@{text "n div 2"}}, @{term take} und @{term drop}, where
  @{term "take n xs"} returns the first @{text n} elements of @{text xs} and
  @{text "drop n xs"} the remainder.

  \item Here are some potentially useful lemmas:\\
    @{text "linorder_not_le:"} @{thm linorder_not_le [no_vars]}\\
    @{text "order_less_le:"} @{thm order_less_le [no_vars]}\\
    @{text "min_def:"} @{thm min_def [no_vars]}
  \end{itemize}
*}

(*<*) end (*>*)
