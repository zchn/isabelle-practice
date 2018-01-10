(*
    $Id: sol.thy,v 1.3 2011/06/28 18:11:39 webertj Exp $
    Author: Martin Strecker
*)

header {* Folding Lists and Trees *}

(*<*) theory sol imports Main begin (*>*)

subsubsection {* Some more list functions *}

text {* Recall the summation function *}

primrec sum :: "nat list \<Rightarrow> nat" where
  "sum [] = 0"
| "sum (x # xs) = x + sum xs"

text {* In the Isabelle library, you will find (in the theory {\tt List.thy})
the functions @{text foldr} and @{text foldl}, which allow you to define some
list functions, among them @{text sum} and @{text length}.  Show the following:
*}

lemma sum_foldr: "sum xs = foldr (op +) xs 0"
  apply (induct xs)
  apply auto
done

lemma length_foldr: "length xs = foldr (\<lambda> x res. 1 + res) xs 0"
  apply (induct xs)
  apply auto
done


text {* Repeated application of @{text foldr} and @{text map} has the
disadvantage that a list is traversed several times.  A single traversal is
sufficient, as illustrated by the following example: *}

lemma "sum (map (\<lambda> x. x + 3) xs) = foldr h xs b"
(*<*) oops (*>*)

text {* Find terms @{text h} and @{text b} which solve this equation. *}

lemma "sum (map (\<lambda> x. x + 3) xs) = foldr (\<lambda> x y. x + y + 3) xs 0"
  apply (induct xs)
  apply auto
done


text {* Generalize this result, i.e.\ show for appropriate @{text h} and @{text
b}: *}

lemma "foldr g (map f xs) a = foldr h xs b"
(*<*) oops (*>*)

text {* Hint: Isabelle can help you find the solution if you use the equalities
arising during a proof attempt. *}

lemma "foldr g (map f xs) a = foldr (\<lambda>x acc. g (f x) acc) xs a"
  apply (induct xs)
  apply auto
done


text {* The following function @{text rev_acc} reverses a list in linear time:
*}

primrec rev_acc :: "['a list, 'a list] \<Rightarrow> 'a list" where
  "rev_acc [] ys = ys"
| "rev_acc (x#xs) ys = (rev_acc xs (x#ys))"

text {* Show that @{text rev_acc} can be defined by means of @{text foldl}. *}

lemma rev_acc_foldl_aux [rule_format]:
  "\<forall>a. rev_acc xs a = foldl (\<lambda> ys x. x # ys) a xs"
  apply (induct xs)
  apply auto
done

lemma rev_acc_foldl: "rev_acc xs a = foldl (\<lambda> ys x. x # ys) a xs"
  by (rule rev_acc_foldl_aux)


text {* Prove the following distributivity property for @{text sum}: *}

lemma sum_append [simp]: "sum (xs @ ys) = sum xs + sum ys"
  apply (induct xs)
  apply auto
done


text {* Prove a similar property for @{text foldr}, i.e.\ something like @{text
"foldr f (xs @ ys) a = f (foldr f xs a) (foldr f ys a)"}.  However, you will
have to strengthen the premises by taking into account algebraic properties of
@{text f} and @{text a}. *}

definition
  left_neutral :: "['a \<Rightarrow> 'b \<Rightarrow> 'b, 'a] \<Rightarrow> bool" where
  "left_neutral f a == (\<forall> x. (f a x = x))"

definition
  assoc :: "['a \<Rightarrow> 'a \<Rightarrow> 'a] \<Rightarrow> bool" where
  "assoc f == (\<forall> x y z. f (f x y) z = f x (f y z))"

lemma foldr_append:
  "\<lbrakk> left_neutral f a; assoc f \<rbrakk> \<Longrightarrow> foldr f (xs @ ys) a = f (foldr f xs a) (foldr f ys a)"
  apply (induct xs)
    apply (simp add: left_neutral_def)
  apply (simp add: assoc_def)
done


text {* Now, define the function @{text prod}, which computes the product of
all list elements *}

(*<*) consts (*>*)
  prod :: "nat list \<Rightarrow> nat"

defs
  prod_def: "prod xs == foldr (op *) xs 1"

text {* directly with the aid of a fold and prove the following: *}

lemma "prod (xs @ ys) = prod xs * prod ys"
  apply (simp only: prod_def)
  apply (rule foldr_append)
    apply (simp add: left_neutral_def)
  apply (simp add: assoc_def)
done


subsubsection {* Functions on Trees *}

text {* Consider the following type of binary trees: *}

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

text {* Define functions which convert a tree into a list by traversing it in
pre-, resp.\ postorder: *}

primrec preorder :: "'a tree \<Rightarrow> 'a list" where
  "preorder Tip          = []"
| "preorder (Node l x r) = x # ((preorder l) @ (preorder r))"

primrec postorder :: "'a tree \<Rightarrow> 'a list" where
  "postorder Tip          = []"
| "postorder (Node l x r) =  (postorder l) @ (postorder r) @ [x]"


text {* You have certainly realized that computation of postorder traversal can
be efficiently realized with an accumulator, in analogy to @{text rev_acc}: *}

primrec postorder_acc :: "['a tree, 'a list] \<Rightarrow> 'a list" where
  "postorder_acc Tip          xs = xs"
| "postorder_acc (Node l x r) xs = (postorder_acc l (postorder_acc r (x#xs)))"


text {* Define this function and show: *}

lemma postorder_acc_aux [rule_format]:
  "\<forall>xs. postorder_acc t xs = (postorder t) @ xs"
  apply (induct t)
  apply auto
done

lemma "postorder_acc t xs = (postorder t) @ xs"
  by (rule postorder_acc_aux)


text {* @{text postorder_acc} is the instance of a function @{text foldl_tree},
which is similar to @{text foldl}. *}

primrec foldl_tree :: "('b => 'a => 'b) \<Rightarrow> 'b \<Rightarrow> 'a tree \<Rightarrow> 'b" where
  "foldl_tree f a Tip          = a"
| "foldl_tree f a (Node l x r) = (foldl_tree f (foldl_tree f (f a x) r) l)"


text {* Show the following: *}

lemma "\<forall> a. postorder_acc t a = foldl_tree (\<lambda> xs x. Cons x xs) a t"
  apply (induct t)
  apply auto
done


text {* Define a function @{text tree_sum} that computes the sum of the
elements of a tree of natural numbers: *}

primrec tree_sum :: "nat tree \<Rightarrow> nat" where
  "tree_sum Tip          = 0"
| "tree_sum (Node l x r) = (tree_sum l) + x + (tree_sum r)"


text {* and show that this function satisfies *}

lemma "tree_sum t = sum (preorder t)"
  apply (induct t)
  apply auto
done


(*<*) end (*>*)
