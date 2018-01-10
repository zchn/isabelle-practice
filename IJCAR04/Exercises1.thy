theory Exercises1 imports Main begin

lemma "A \<or> B \<longrightarrow> B \<or> A"
  apply(rule impI)
  apply(erule disjE)
   apply(rule disjI2)
   apply(assumption)
  apply(rule disjI1)
  apply(assumption)
  done

lemma "\<lbrakk> A \<longrightarrow> B; B \<longrightarrow> C \<rbrakk> \<Longrightarrow> A \<longrightarrow> C"
  apply(rule impI)
  apply(erule impE)
   apply(assumption)
  apply(erule impE)
   apply(assumption)
  apply(assumption)
  done

text {* 
  use constdefs to define a new constant @{text or} that 
  defines @{text "\<or>"} by conjunction and negation 
*}

definition or :: "bool \<Rightarrow> bool \<Rightarrow> bool" where
"or a b == \<not>(\<not>a \<and> \<not>b)"

thm notI notE

lemma "A \<or> B \<Longrightarrow> or A B"
  apply (unfold or_def)
  apply(rule notI)
  apply(erule disjE)
   apply(erule conjE)
   apply(erule notE)
   apply(assumption)
  apply(erule conjE)
  apply(erule notE)
  apply(erule notE)
  apply(assumption)
  done

thm ccontr notI notE

lemma "or A B \<Longrightarrow> A \<or> B"
  apply(unfold or_def)
  apply(rule ccontr)
  apply(erule notE)
  apply(rule conjI)
   apply(rule notI)
   apply(erule notE)
   apply(rule disjI1)
   apply(assumption)
  apply(rule notI)
  apply(erule notE)
  apply(rule disjI2)
  apply(assumption)
  done

thm allI allE exI exE impI impE

lemma "(\<exists>a. \<forall>b. P a b) \<longrightarrow> (\<forall>d. \<exists>c. P c d)"
  apply(rule impI)
  apply(rule allI)

lemma "((\<exists>x. P x) \<longrightarrow> Q) \<longrightarrow> (\<forall>x. P x \<longrightarrow> Q)" 
oops

lemma "\<exists>x. (P x \<longrightarrow> (\<forall>x. P x))"
oops

end
