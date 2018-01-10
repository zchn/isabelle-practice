theory Demo2 imports Main begin

subsection "data types"

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

lemma "Tip \<noteq> Node l x r"
apply simp
done

lemma "(1::nat) \<le> (case t of Tip \<Rightarrow> 1 | Node l x r \<Rightarrow> x+1)"
apply(case_tac t)
apply auto
done


subsection "induction heuristics"

consts itrev :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
primrec
  "itrev [] ys = ys"
  "itrev (x#xs) ys = itrev xs (x#ys)"


lemma "itrev xs [] = rev xs"
  
























oops
-- solution

lemma "ALL ys. itrev xs ys = rev xs @ ys"
apply(induct xs)
apply(auto)
done

end
