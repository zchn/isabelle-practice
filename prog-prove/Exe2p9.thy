theory Exe2p9
  imports Main
begin

fun itadd :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"itadd 0 n = n" |
"itadd (Suc m) n = itadd m (Suc n)"

lemma "itadd m n = m + n"
  apply(induction m arbitrary: n)
   apply(auto)
  done

end
