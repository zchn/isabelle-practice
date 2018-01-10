theory S1Demo2 imports Main begin

section{* Propositional logic *}

subsection{* Basic rules *}

text{* \<and> *}
thm conjI conjE 

text{* \<or> *}
thm disjI1 disjI2 disjE

text{* \<longrightarrow> *}
thm impI impE


subsection{* Examples *}

text{* a simple backward step: *}
lemma "A \<and> B"
apply(rule conjI)
oops

text{* a simple backward proof: *}
lemma "B \<and> A \<longrightarrow> A \<and> B"
apply(rule impI)
apply(erule conjE)
apply(rule conjI)
 apply(assumption)
apply(assumption)
done


end
