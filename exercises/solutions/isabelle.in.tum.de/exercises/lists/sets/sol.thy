(*
    $Id: sol.thy,v 1.4 2011/06/28 18:11:38 webertj Exp $
    Author: Martin Strecker
*)

header {* Sets as Lists *}

(*<*) theory sol imports Main begin (*>*)

text {* Finite sets can obviously be implemented by lists.  In the
following, you will be asked to implement the set operations union,
intersection and difference and to show that these implementations are
correct.  Thus, for a function *}


primrec list_union :: "['a list, 'a list] \<Rightarrow> 'a list" where
  "list_union xs []     = xs"
| "list_union xs (y#ys) = (let result = list_union xs ys in if y : set result then result else y#result)"

text {* to be defined by you it has to be shown that *}

lemma "set (list_union xs ys) = set xs \<union> set ys"
  apply (induct "ys")
    apply simp
  apply (simp add: Let_def)
  apply auto
done

text {* In addition, the functions should be space efficient in the
sense that one obtains lists without duplicates (@{text "distinct"})
whenever the parameters of the functions are duplicate-free.  Thus, for
example, *}

lemma [rule_format]: 
  "distinct xs \<longrightarrow> distinct ys \<longrightarrow> (distinct (list_union xs ys))"
  apply (induct "ys")
  apply (auto simp add: Let_def)
done

text {* \emph{Hint:} @{text "distinct"} is defined in @{text List.thy}. *}

text {* We omit the definitions and correctness proofs for set
intersection and set difference. *}


subsubsection {* Quantification over Sets *}

text {* Define a (non-trivial) set @{text S} such that the following
proposition holds: *}

lemma "((\<forall> x \<in> A. P x) \<and> (\<forall> x \<in> B. P x)) \<longrightarrow> (\<forall> x \<in> S. P x)"
(*<*)oops(*>*)

lemma "((\<forall> x \<in> A. P x) \<and> (\<forall> x \<in> B. P x)) \<longrightarrow> (\<forall> x \<in> A\<union>B. P x)"
  by auto

text {* Define a (non-trivial) predicate @{text P} such that *}

lemma "\<forall> x \<in> A. P (f x) \<Longrightarrow>  \<forall> y \<in> f ` A. Q y"
(*<*)oops(*>*)

lemma "\<forall> x \<in> A. Q (f x) \<Longrightarrow>  \<forall> y \<in> f ` A. Q y"
  by auto

(*<*) end (*>*)
