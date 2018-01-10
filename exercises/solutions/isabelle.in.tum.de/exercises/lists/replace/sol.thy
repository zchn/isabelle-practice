(*
    $Id: sol.thy,v 1.3 2011/06/28 18:11:38 webertj Exp $
*)

header {* Replace, Reverse and Delete *}

(*<*) theory sol imports Main begin (*>*)

text{*
Define a function @{term replace}, such that @{term"replace x y zs"}
yields @{term zs} with every occurrence of @{term x} replaced by @{term y}.
*}

primrec replace :: "'a \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "replace x y []     = []"
| "replace x y (z#zs) = (if z=x then y else z)#(replace x y zs)"

text {*
Prove or disprove (by counterexample) the following theorems.
You may have to prove some lemmas first.
*}

lemma replace_append: "replace x y (xs @ ys) = replace x y xs @ replace x y ys"
  apply (induct "xs")
  apply auto
done

theorem "rev(replace x y zs) = replace x y (rev zs)"
  apply (induct "zs")
  apply (auto simp add: replace_append)
done

theorem "replace x y (replace u v zs) = replace u v (replace x y zs)"
  quickcheck
oops

text {*
  A possible counterexample:
  u=0, v=1, x=0, y=-1, zs=[0]
*}

theorem "replace y z (replace x y zs) = replace x z zs"
  quickcheck
oops

text {*
  A possible counterexample:
  x=1, y=0, z=1, zs=[0]
*}

text{* Define two functions for removing elements from a list:
@{term"del1 x xs"} deletes the first occurrence (from the left) of
@{term x} in @{term xs}, @{term"delall x xs"} all of them. *}

primrec del1 :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "del1 x []     = []"
| "del1 x (y#ys) = (if y=x then ys else y # del1 x ys)"

primrec delall :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "delall x []     = []"
| "delall x (y#ys) = (if y=x then delall x ys else y # delall x ys)"

text {*
Prove or disprove (by counterexample) the following theorems.
*}

theorem "del1 x (delall x xs) = delall x xs"
  apply (induct "xs")
  apply auto
done

theorem "delall x (delall x xs) = delall x xs"
  apply (induct "xs")
  apply auto
done

theorem delall_del1: "delall x (del1 x xs) = delall x xs"
  apply (induct "xs")
  apply auto
done

theorem "del1 x (del1 y zs) = del1 y (del1 x zs)"
  apply (induct "zs")
  apply auto
done

theorem "delall x (del1 y zs) = del1 y (delall x zs)"
  apply (induct "zs")
  apply (auto simp add: delall_del1)
done

theorem "delall x (delall y zs) = delall y (delall x zs)"
  apply (induct "zs")
  apply auto
done

theorem "del1 y (replace x y xs) = del1 x xs"
  quickcheck
oops

text {*
  A possible counterexample:
  x=1, xs=[0], y=0
*}

theorem "delall y (replace x y xs) = delall x xs"
  quickcheck
oops

text {*
  A possible counterexample:
  x=1, xs=[0], y=0
*}

theorem "replace x y (delall x zs) = delall x zs"
  apply (induct "zs")
  apply auto
done

theorem "replace x y (delall z zs) = delall z (replace x y zs)"
  quickcheck
oops

text {*
  A possible counterexample:
  x=1, y=0, z=0, zs=[1]
*}

theorem "rev(del1 x xs) = del1 x (rev xs)"
  quickcheck
oops

text {*
  A possible counterexample:
  x=1, xs=[1, 0, 1]
*}

lemma delall_append: "delall x (xs @ ys) = delall x xs @ delall x ys"
  apply (induct "xs")
  apply auto
done

theorem "rev(delall x xs) = delall x (rev xs)"
  apply (induct "xs")
  apply (auto simp add: delall_append)
done

(*<*) end (*>*)
