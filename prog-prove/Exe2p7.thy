theory Exe2p7
  imports Main
begin

datatype 'a tree2 = Tip 'a | Node "'a tree2" 'a "'a tree2"

fun mirror :: "'a tree2 \<Rightarrow> 'a tree2" where
"mirror (Tip a) = Tip a" |
"mirror (Node l n r) = Node (mirror r) n (mirror l)"

fun pre_order :: "'a tree2 \<Rightarrow> 'a list" where
"pre_order (Tip a) = [a]" |
"pre_order (Node l n r) = n # (pre_order l) @ (pre_order r)"

fun post_order :: "'a tree2 \<Rightarrow> 'a list" where
"post_order (Tip a) = [a]" |
"post_order (Node l n r) = (post_order l) @ (post_order r) @ [n]"

lemma pre_m_rev_post : "pre_order (mirror t) = rev (post_order t)"
  apply(induction t)
   apply(auto)
  done

end
