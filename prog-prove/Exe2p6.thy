theory Exe2p6 
  imports Main
begin

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun contents :: "'a tree \<Rightarrow> 'a list" where
"contents Tip = []" |
"contents (Node l n r) = n # (contents l) @ (contents r)"

fun sum_tree :: "nat tree \<Rightarrow> nat" where
"sum_tree Tip = 0" |
"sum_tree (Node l n r) = n + sum_tree l + sum_tree r"

lemma sum_tree_lemma_1 : "sum_tree t = sum_list (contents t)"
  apply(induction t rule: sum_tree.induct)
   apply(auto)
  done

end
