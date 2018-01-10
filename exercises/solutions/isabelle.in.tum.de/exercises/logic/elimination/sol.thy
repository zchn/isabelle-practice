(*
    $Id: sol.thy,v 1.3 2006/10/04 23:48:20 kleing Exp $
    Author: Martin Strecker
*)

header {* Elimination of Connectives *}

(*<*) theory sol imports Main begin (*>*)

text {* In classical propositional logic, the connectives @{text "=, \<or>,
\<not>"} can be replaced by @{text "\<longrightarrow>, \<and>, False"}.  Define
corresponding simplification rules as lemmas and prove their correctness.  (You
may use automated proof tactics.) *}

lemma equiv_conel: "(A = B) = ((A \<longrightarrow> B) \<and> (B \<longrightarrow> A))"
  by iprover

lemma or_conel: "(A \<or> B) = (\<not> (\<not> A \<and> \<not> B))"
  by blast

lemma not_conel: "(\<not> A) = (A \<longrightarrow> False)"
  by blast


text {* What is the result of your translation for the formula @{text "A \<or>
(B \<and> C) = A"}?  (You can use Isabelle's simplifier to compute the result
by using the simplifier's @{text "only"} option.) *}

text {* Stating @{text "A \<or> (B \<and> C) = A"} as a lemma and application
of\\
@{text "(simp only: equiv_conel or_conel not_conel)"}\\
results in the simplified goal\\
@{text "(A \<longrightarrow> False) \<and> ((B \<and> C \<longrightarrow> A)
\<and> (A \<longrightarrow> B \<and> C) \<longrightarrow> False)
\<longrightarrow> False"}. *}


(*<*) end (*>*)
