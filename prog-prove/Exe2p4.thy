theory Exe2p4
  imports Main
begin

fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
"snoc [] a = [a]" |
"snoc (h # t) a = h # (snoc t a)"

fun reverse :: "'a list \<Rightarrow> 'a list" where
"reverse [] = []" | 
"reverse (h # t) = snoc (reverse t) h"

lemma [simp]: "reverse (snoc xs x) = x # (reverse xs)"
  apply(induction xs)
   apply(auto)
  done

lemma rev_rev_id : "reverse (reverse xs) = xs"
  apply(induction xs)
   apply(auto)
  done

end