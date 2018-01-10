theory Exe2p3
  imports Main
begin

fun count :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
"count a [] = 0" |
"count a (b # t) = (if a = b then count a t + 1 else count a t)"

lemma count_le_length: "count x xs \<le> length xs"
  apply(induction xs)
   apply(auto)
  done

end