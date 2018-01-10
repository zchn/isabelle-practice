theory Exe2p5
  imports Main
begin

fun sum_upto :: "nat \<Rightarrow> nat" where
"sum_upto 0 = 0" |
"sum_upto (Suc n) = sum_upto n + n + 1"

lemma simp_sum_upto: "sum_upto n = n * (n + 1) div 2"
  apply(induction n)
   apply(auto)
  done
