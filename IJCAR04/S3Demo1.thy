theory Demo1 imports Main begin

subsection {* @{text "?thesis"}, @{text this}, \isakeyword{then} *}

lemma "A \<and> B \<longrightarrow> B \<and> A"
proof
  assume "A \<and> B"
  from this show "B \<and> A"
  proof
    assume "A" "B"
    show ?thesis ..
  qed
qed

subsection {* \isakeyword{with} *}

lemma "A \<and> B \<longrightarrow> B \<and> A"
proof
  assume ab: "A \<and> B"
  from ab have a: "A" ..
  from ab have b: "B" ..
  from b a show "B \<and> A" ..
qed


subsection{*Predicate calculus*}

text{* \isakeyword{fix} *}

lemma "\<forall>x. P x \<Longrightarrow> \<forall>x. P(f x)"
proof 
  fix a
  assume "\<forall>x. P x"
  then show "P(f a)" ..  
qed

lemma "\<exists>x. P(f x) \<Longrightarrow> \<exists>y. P y"
proof -
  assume "\<exists>x. P(f x)"
  then show ?thesis
  proof              
    fix x
    assume "P(f x)"
    show ?thesis ..  
  qed
qed

text{* \isakeyword{obtain} *}

lemma "\<exists>x. P(f x) \<Longrightarrow> \<exists>y. P y"
proof -
  assume "\<exists>x. P(f x)"
  then obtain x where "P(f x)" ..
  then show "\<exists>y. P y" ..
qed

end
