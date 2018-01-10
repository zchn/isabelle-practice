theory Demo4 imports Main begin

subsection{*Inductive definition of the even numbers*}

consts Ev :: "nat set"
inductive Ev
intros
ZeroI: "0 \<in> Ev"
Add2I: "n \<in> Ev \<Longrightarrow> Suc(Suc n) \<in> Ev"


text{* Using the introduction rules: *}
lemma "Suc(Suc(Suc(Suc 0))) \<in> Ev"
apply(rule Add2I)
apply(rule Add2I)
apply(rule ZeroI)
done


text{*A simple inductive proof: *}
lemma "n \<in> Ev \<Longrightarrow> n+n \<in> Ev"
apply(erule Ev.induct)
 apply(simp)
 apply(rule ZeroI)
apply(simp)
apply(rule Add2I)
apply(rule Add2I)
apply(assumption)
done


end
