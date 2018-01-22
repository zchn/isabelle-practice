(*  Title:      HOL/Isar_Examples/Drinker.thy
    Author:     Makarius
*)

section \<open>The Drinker's Principle\<close>

theory Drinker
  imports Main
begin

text \<open>
  Here is another example of classical reasoning: the Drinker's Principle says
  that for some person, if he is drunk, everybody else is drunk!

  We first prove a classical part of de-Morgan's law.
\<close>

lemma de_Morgan:
  assumes "\<not> (\<forall>x. P x)"
  shows "\<exists>x. \<not> P x"
proof (rule classical)
  assume "\<nexists>x. \<not> P x"
  hence "\<forall>x. P x" by blast
  with assms show ?thesis by contradiction
qed

theorem Drinker's_Principle: "\<exists>x. drunk x \<longrightarrow> (\<forall>x. drunk x)"
proof (cases "\<forall>x. drunk x")
  case True
  then show ?thesis by blast
next
  case False
  then show ?thesis by blast
qed
  
end
