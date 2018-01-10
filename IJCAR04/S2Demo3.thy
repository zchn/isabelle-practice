theory Demo3 imports Main begin

consts sep :: "'a \<times> 'a list \<Rightarrow> 'a list"
recdef sep "measure (\<lambda>(a, xs). size xs)"
  "sep (a, x#y#zs) = x # a # sep (a,y#zs)"
  "sep (a, xs) = xs"

print_theorems

lemma "map f (sep (x,xs)) = sep (f x, map f xs)"


















oops
-- solution

lemma "map f (sep (x,xs)) = sep (f x, map f xs)"
  apply (induct x xs rule: sep.induct)
  apply auto
  done

end
