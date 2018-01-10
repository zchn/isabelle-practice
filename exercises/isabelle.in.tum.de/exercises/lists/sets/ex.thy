(*
    $Id: ex.thy,v 1.3 2011/06/28 18:11:38 webertj Exp $
    Author: Martin Strecker
*)

header {* Sets as Lists *}

(*<*) theory ex imports Main begin (*>*)

text {* Finite sets can obviously be implemented by lists.  In the
following, you will be asked to implement the set operations union,
intersection and difference and to show that these implementations are
correct.  Thus, for a function *}

(*<*)consts(*>*)
  list_union :: "['a list, 'a list] \<Rightarrow> 'a list"

text {* to be defined by you it has to be shown that *}

lemma "set (list_union xs ys) = set xs \<union> set ys"
(*<*)oops(*>*)

text {* In addition, the functions should be space efficient in the
sense that one obtains lists without duplicates (@{text "distinct"})
whenever the parameters of the functions are duplicate-free.  Thus, for
example, *}

lemma [rule_format]: 
  "distinct xs \<longrightarrow> distinct ys \<longrightarrow> (distinct (list_union xs ys))"
(*<*)oops(*>*)

text {* \emph{Hint:} @{text "distinct"} is defined in @{text List.thy}. *}


subsubsection {* Quantification over Sets *}

text {* Define a (non-trivial) set @{text S} such that the following
proposition holds: *}

lemma "((\<forall> x \<in> A. P x) \<and> (\<forall> x \<in> B. P x)) \<longrightarrow> (\<forall> x \<in> S. P x)"
(*<*)oops(*>*)

text {* Define a (non-trivial) predicate @{text P} such that *}

lemma "\<forall> x \<in> A. P (f x) \<Longrightarrow>  \<forall> y \<in> f ` A. Q y"
(*<*)oops(*>*)

(*<*) end (*>*)
