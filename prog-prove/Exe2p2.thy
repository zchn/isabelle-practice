theory Exe2p2
  imports Main
begin

fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add 0 n = n" |
"add (Suc m) n = Suc (add m n)"

lemma [simp]: "add a 0 = a"
  apply(induction a)
   apply(auto)
  done


lemma add_assoc: "add (add a b) c = add a (add b c)"
  apply(induction a)
   apply(auto)
  done

lemma [simp]: "add b (Suc a) = Suc (add b a)"
  apply(induction b)
   apply(auto)
  done

lemma add_comm: "add a b = add b a"
  apply(induction a)
   apply(auto)
  done

end