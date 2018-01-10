theory Demo5 imports Main begin

subsection{* Propositional logic, introduction rules *}

lemma "A \<longrightarrow> A" 
proof (rule impI) 
  assume "A" 
  show "A" by assumption
qed

text{* \isakeyword{proof} *}

lemma "A \<longrightarrow> A"
proof 
  assume A
  show A by assumption
qed


text{* \isakeyword{.} *}

lemma "A \<longrightarrow> A"
proof
  assume "A"
  show "A" .
qed

text{* \isakeyword{by} *}

lemma "A \<longrightarrow> A" by (rule impI)

lemma "A \<longrightarrow> A \<and> A"
proof
  assume "A"
  show "A \<and> A" by (rule conjI)
qed

text{* \isakeyword{..} *}

lemma "A \<longrightarrow> A \<and> A"
proof
  assume "A"
  show "A \<and> A" ..
qed



subsubsection{*Elimination rules*}

lemma "A \<and> B \<longrightarrow> B \<and> A"
proof
  assume AB: "A \<and> B"
  from AB show "B \<and> A"
  proof
    assume "A" "B"
    show "B \<and> A" ..
  qed
qed


end
