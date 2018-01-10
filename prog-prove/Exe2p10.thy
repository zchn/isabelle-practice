theory Exe2p10
  imports Main
begin

datatype tree0 = Tip | Node tree0 tree0

fun nodes :: "tree0 \<Rightarrow> nat" where
"nodes Tip = 1" |
"nodes (Node l r) = 1 + nodes l + nodes r"

fun explode :: "nat \<Rightarrow> tree0 \<Rightarrow> tree0" where
"explode 0 t = t" |
"explode (Suc n) t = explode n (Node t t)"

lemma "(nodes (explode n t)) = (nodes t + 1) * (2 ^ n) - 1"
  apply(induction n arbitrary: t)
   apply(auto)
  apply(simp add: algebra_simps)
  done

end
