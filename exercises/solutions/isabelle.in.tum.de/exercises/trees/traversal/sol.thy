(*
    $Id: sol.thy,v 1.3 2011/06/28 18:11:39 webertj Exp $
    Author: Farhad Mehta, Tobias Nipkow
*)

header {* Tree Traversal *}

(*<*) theory sol imports Main begin (*>*)

text {* Define a datatype @{text"'a tree"} for binary trees. Both leaf and
internal nodes store information. *}

datatype 'a tree = Tip "'a" | Node "'a" "'a tree" "'a tree"


text {* Define the functions @{term preOrder}, @{term postOrder}, and @{term
inOrder} that traverse an @{text"'a tree"} in the respective order. *}

primrec preOrder :: "'a tree \<Rightarrow> 'a list" where
  "preOrder (Tip a)      = [a]"
| "preOrder (Node f x y) = f#((preOrder x)@(preOrder y))"

primrec postOrder :: "'a tree \<Rightarrow> 'a list" where
  "postOrder (Tip a)      = [a]"
| "postOrder (Node f x y) = (postOrder x)@(postOrder y)@[f]"

primrec inOrder :: "'a tree \<Rightarrow> 'a list" where
  "inOrder (Tip a)      = [a]"
| "inOrder (Node f x y) = (inOrder x)@[f]@(inOrder y)"


text {* Define a function @{term mirror} that returns the mirror image of an
@{text "'a tree"}. *}

primrec mirror :: "'a tree \<Rightarrow> 'a tree" where
  "mirror (Tip a)      = (Tip a)"
| "mirror (Node f x y) = (Node f (mirror y) (mirror x))"


text {* Suppose that @{term xOrder} and @{term yOrder} are tree traversal
functions chosen from @{term preOrder}, @{term postOrder}, and @{term inOrder}.
Formulate and prove all valid properties of the form \mbox{@{text "xOrder
(mirror xt) = rev (yOrder xt)"}}. *}

theorem  "preOrder (mirror xt) = rev (postOrder xt)"
  apply (induct_tac xt)
  apply auto
done

theorem "postOrder (mirror xt) = rev (preOrder xt)"
  apply (induct_tac xt)
  apply auto
done

theorem "inOrder (mirror xt) = rev (inOrder xt)"
  apply (induct_tac xt)
  apply auto
done


text {* Define the functions @{term root}, @{term leftmost} and @{term
rightmost}, that return the root, leftmost, and rightmost element respectively.
*}

primrec root :: "'a tree \<Rightarrow> 'a" where
  "root (Tip a)      = a"
| "root (Node f x y) = f"

primrec leftmost :: "'a tree \<Rightarrow> 'a" where
  "leftmost (Tip a)      = a"
| "leftmost (Node f x y) = (leftmost x)"

primrec rightmost :: "'a tree \<Rightarrow> 'a" where
  "rightmost (Tip a)      = a"
| "rightmost (Node f x y) = (rightmost y)"


text {* Prove or disprove (by counterexample) the theorems that follow.  You
may have to prove some lemmas first. *}

lemma [simp]: "inOrder xt ~= []"
  apply (induct_tac xt)
  apply auto
done

lemma [simp]: "ys ~= [] \<longrightarrow> last (xs @ ys) = last ys"
  apply (induct_tac xs)
  apply auto
done

theorem "last (inOrder xt) = rightmost xt"
  apply (induct_tac xt)
  apply auto
done

theorem "hd (inOrder xt) = leftmost xt"
  apply (induct_tac xt)
  apply auto
done

theorem "hd (preOrder xt) = last (postOrder xt)"
  apply (induct_tac xt)
  apply auto
done

theorem "hd (preOrder xt) = root xt"
  apply (induct_tac xt)
  apply auto
done

theorem "hd (inOrder xt) = root xt"
  quickcheck
oops

text {*
  Counterexample found: \\
  xt = Node 1 (Tip 0) (Tip 0)
*}

theorem "last (postOrder xt) = root xt"
  apply (induct_tac xt)
  apply auto
done


(*<*) end (*>*)
