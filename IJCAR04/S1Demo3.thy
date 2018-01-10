theory S1Demo3 imports Main begin

section{* Predicate logic *}

subsection{* Quantifier reasoning *}

text{* A successful proof: *}
lemma "\<forall>x. \<exists>y. x = y"
apply(rule allI)
apply(rule exI)
thm refl
apply(rule refl)
done

text{* An unsuccessful proof: *}
lemma "\<exists>y. \<forall>x. x = y"
apply(rule exI)
apply(rule allI)
(* Does not work:
apply(rule refl)
*)
oops

text{* Intro and elim resoning: *}
lemma "\<exists>y. \<forall>x. P x y \<Longrightarrow> \<forall>x. \<exists>y. P x y"
(* the safe rules first: *)
apply(rule allI)
apply(erule exE)
(* now the unsafe ones: *)
apply(rule_tac x=y in exI)
apply(erule_tac x=x in allE)
apply(assumption)
done

text{* What happens if an unsafe rule is tried too early: *}
lemma "\<exists>y. \<forall>x. P x y \<Longrightarrow> \<forall>x. \<exists>y. P x y"
apply(rule allI)
apply(rule exI)
apply(erule exE)
apply(erule allE)
(* Fails now:
apply(assumption)
*)
oops


subsubsection{* Forward reasoning *}

lemma "A \<and> B \<Longrightarrow> \<not> \<not> A"
thm conjunct1
apply(drule conjunct1)
apply blast
done


subsubsection{* Automation *}

lemma "\<forall>x y. P x y \<and> Q x y \<and> R x y"
apply(intro allI conjI)
oops

lemma "\<forall>x y. P x y \<and> Q x y \<and> R x y"
apply(clarify)
oops

lemma "\<exists>y. \<forall>x. P x y \<Longrightarrow> \<forall>x. \<exists>y. P x y"
apply blast
done

end
