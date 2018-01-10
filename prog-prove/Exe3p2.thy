theory Exe3p2
  imports Main
begin

inductive palindrome :: "int list \<Rightarrow> bool" where
palin_zero: "palindrome []" |
palin_one: "palindrome [x]" |
palin_step: "palindrome xs \<Longrightarrow> palindrome (x#xs@[x])"

lemma "palindrome xs \<Longrightarrow> rev xs = xs"
  apply(induction rule: palindrome.induct)
  by auto

end