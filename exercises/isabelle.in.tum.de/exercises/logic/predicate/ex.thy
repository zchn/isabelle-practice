(*
    $Id: ex.thy,v 1.2 2004/11/23 15:14:35 webertj Exp $
*)

header {* Predicate Logic *}

(*<*) theory ex imports Main begin (*>*)

text {*
We are again talking about proofs in the calculus of Natural Deduction.  In
addition to the rules given in the exercise ``Propositional Logic'', you may
now also use

  @{text "exI:"}~@{thm exI[no_vars]}\\
  @{text "exE:"}~@{thm exE[no_vars]}\\
  @{text "allI:"}~@{thm allI[no_vars]}\\
  @{text "allE:"}~@{thm allE[no_vars]}\\

Give a proof of the following propositions or an argument why the formula is
not valid:
*}

lemma "(\<exists>x. \<forall>y. P x y) \<longrightarrow> (\<forall>y. \<exists>x. P x y)"
(*<*) oops (*>*)

lemma "(\<forall>x. P x \<longrightarrow> Q) = ((\<exists>x. P x) \<longrightarrow> Q)"
(*<*) oops (*>*)

lemma "((\<forall> x. P x) \<and> (\<forall> x. Q x)) = (\<forall> x. (P x \<and> Q x))"
(*<*) oops (*>*)

lemma "((\<forall> x. P x) \<or> (\<forall> x. Q x)) = (\<forall> x. (P x \<or> Q x))"
(*<*) oops (*>*)

lemma "((\<exists> x. P x) \<or> (\<exists> x. Q x)) = (\<exists> x. (P x \<or> Q x))"
(*<*) oops (*>*)

lemma "(\<forall>x. \<exists>y. P x y) \<longrightarrow> (\<exists>y. \<forall>x. P x y)"
(*<*) oops (*>*)

lemma "(\<not> (\<forall> x. P x)) = (\<exists> x. \<not> P x)"
(*<*) oops (*>*)

(*<*) end (*>*)
