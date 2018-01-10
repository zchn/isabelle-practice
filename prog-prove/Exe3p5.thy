theory Exe3p5
  imports Main
begin

datatype alpha = a | b

inductive S :: "alpha list \<Rightarrow> bool" where
s_empty: "S []" |
s_aSb: "S w \<Longrightarrow> S (a # w @ [b])" |
s_SS: "S w1 \<Longrightarrow> S w2 \<Longrightarrow> S (w1 @ w2)"

inductive T :: "alpha list \<Rightarrow> bool" where
t_empty: "T []" |
t_TaTb: "T w1 \<Longrightarrow> T w2 \<Longrightarrow> T (w1 @ [a] @ w2 @ [b])"

lemma "T w \<Longrightarrow> T (a # w @ [b])"
  apply(induction rule: T.induct)
   apply(auto simp add: t_empty t_TaTb)
  oops

lemma "T w = S w"
  apply(rule iffI)
   apply(induction rule: T.induct)
    apply(auto simp add: s_empty s_aSb s_SS)
  apply(induction rule: S.induct)
    apply(auto simp add: t_empty t_TaTb)
  oops