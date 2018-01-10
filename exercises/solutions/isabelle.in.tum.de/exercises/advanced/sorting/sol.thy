(*
    $Id: sol.thy,v 1.3 2011/06/28 18:11:37 webertj Exp $
    Author: Gerwin Klein
*)

header {* Sorting with Lists and Trees *}

(*<*) theory sol imports Main begin (*>*)

text {*
  For simplicity we sort natural numbers.
*}

subsubsection {* Sorting with lists *}

text {*
  The task is to define insertion sort and prove its correctness.  The
  following functions are required:

  @{text "insort :: nat \<Rightarrow> nat list \<Rightarrow> nat list"}\\
  @{text "sort   :: nat list \<Rightarrow> nat list"}\\
  @{text "le     :: nat \<Rightarrow> nat list \<Rightarrow> bool"}\\
  @{text "sorted :: nat list \<Rightarrow> bool"}

  In your definition, @{term "insort x xs"} should insert a number @{term x}
  into an already sorted list @{text xs}, and @{term "sort ys"} should build on
  @{text insort} to produce the sorted version of @{text ys}.

  To show that the resulting list is indeed sorted we need a predicate @{term
  sorted} that checks if each element in the list is less or equal to the
  following ones; @{term "le n xs"} should be true iff @{term n} is less or
  equal to all elements of @{text xs}.
*}

primrec le :: "nat \<Rightarrow> nat list \<Rightarrow> bool" where
  "le a []     = True"
| "le a (x#xs) = (a <= x & le a xs)"

primrec sorted :: "nat list \<Rightarrow> bool" where
  "sorted []     = True"
| "sorted (x#xs) = (le x xs & sorted xs)"

primrec insort :: "nat \<Rightarrow> nat list \<Rightarrow> nat list" where
  "insort a []     = [a]"
| "insort a (x#xs) = (if a <= x then a#x#xs else x # insort a xs)"

primrec sort :: "nat list \<Rightarrow> nat list" where
  "sort []     = []"
| "sort (x#xs) = insort x (sort xs)"


text {*
  Start out by showing a monotonicity property of @{term le}.  For technical
  reasons the lemma should be phrased as follows:
*}

lemma [simp]: "x \<le> y \<Longrightarrow> le y xs \<longrightarrow> le x xs"
  apply (induct_tac xs)
  apply auto
done


text {*
  Now show the following correctness theorem:
*}

lemma [simp]: 
  "le x (insort a xs) = (x <= a & le x xs)"
  apply (induct_tac xs)
  apply auto
done

lemma [simp]:
  "sorted (insort a xs) = sorted xs"
  apply (induct_tac xs)
  apply auto
done

theorem "sorted (sort xs)"
  apply (induct_tac xs)
  apply auto
done


text {*
  This theorem alone is too weak.  It does not guarantee that the sorted list
  contains the same elements as the input.  In the worst case, @{term sort}
  might always return @{term"[]"}~-- surely an undesirable implementation of
  sorting.

  Define a function @{term "count xs x"} that counts how often @{term x} occurs
  in @{term xs}.
*}

primrec count :: "nat list => nat => nat" where
  "count []     y = 0"
| "count (x#xs) y = (if x=y then Suc(count xs y) else count xs y)"


text {*
  Show that
*}

lemma [simp]:
  "count (insort x xs) y =
  (if x=y then Suc (count xs y) else count xs y)"
  apply (induct_tac xs)
  apply auto
done

theorem "count (sort xs) x = count xs x"
  apply (induct_tac xs)
  apply auto
done


subsubsection {* Sorting with trees *}

text {*
  Our second sorting algorithm uses trees.  Thus you should first define a data
  type @{text bintree} of binary trees that are either empty or consist of a
  node carrying a natural number and two subtrees.
*}

datatype bintree = Empty | Node nat bintree bintree


text {*
  Define a function @{text tsorted} that checks if a binary tree is sorted.  It
  is convenient to employ two auxiliary functions @{text tge}/@{text tle} that
  test whether a number is greater-or-equal/less-or-equal to all elements of a
  tree.

  Finally define a function @{text tree_of} that turns a list into a sorted
  tree.  It is helpful to base @{text tree_of} on a function @{term "ins n b"}
  that inserts a number @{term n} into a sorted tree @{term b}.
*}

primrec tge :: "nat \<Rightarrow> bintree \<Rightarrow> bool" where
  "tge x Empty          = True"
| "tge x (Node n t1 t2) = (n \<le> x \<and> tge x t1 \<and> tge x t2)"

primrec tle :: "nat \<Rightarrow> bintree \<Rightarrow> bool" where
  "tle x Empty          = True"
| "tle x (Node n t1 t2) = (x \<le> n \<and> tle x t1 \<and> tle x t2)"

primrec tsorted :: "bintree \<Rightarrow> bool" where
  "tsorted Empty          = True"
| "tsorted (Node n t1 t2) = (tsorted t1 \<and> tsorted t2 \<and> tge n t1 \<and> tle n t2)"

primrec ins :: "nat \<Rightarrow> bintree \<Rightarrow> bintree" where
  "ins x Empty          = Node x Empty Empty"
| "ins x (Node n t1 t2) = (if x \<le> n then Node n (ins x t1) t2 else Node n t1 (ins x t2))"

primrec tree_of :: "nat list \<Rightarrow> bintree" where
  "tree_of []     = Empty"
| "tree_of (x#xs) = ins x (tree_of xs)"


text {*
  Show
*}

lemma [simp]: "tge a (ins x t) = (x \<le> a \<and> tge a t)"
  apply (induct_tac t)
  apply auto
done

lemma [simp]: "tle a (ins x t) = (a \<le> x \<and> tle a t)"
  apply (induct_tac t)
  apply auto
done

lemma [simp]: "tsorted (ins x t) = tsorted t"
  apply (induct_tac t)
  apply auto
done

theorem [simp]: "tsorted (tree_of xs)"
  apply (induct_tac xs)
  apply auto
done


text {*
  Again we have to show that no elements are lost (or added).  As for lists,
  define a function @{term "tcount x b"} that counts the number of occurrences
  of the number @{term x} in the tree @{term b}.
*}

primrec tcount :: "bintree => nat => nat" where
  "tcount Empty          y = 0"
| "tcount (Node x t1 t2) y = (if x=y then
                                Suc (tcount t1 y + tcount t2 y)
                              else
                                tcount t1 y + tcount t2 y)"


text {*
  Show
*}

lemma [simp]: "tcount (ins x t) y =
  (if x=y then Suc (tcount t y) else tcount t y)"
  apply(induct_tac t)
  apply auto
done

theorem "tcount (tree_of xs) x = count xs x"
  apply (induct_tac xs)
  apply auto
done


text {*
  Now we are ready to sort lists.  We know how to produce an ordered tree from
  a list.  Thus we merely need a function @{text list_of} that turns an
  (ordered) tree into an (ordered) list.  Define this function and prove
*}

theorem "sorted (list_of (tree_of xs))"
(*<*) oops (*>*)

theorem "count (list_of (tree_of xs)) n = count xs n"
(*<*) oops (*>*)

text {*
  Hints:
  \begin{itemize}
  \item
  Try to formulate all your lemmas as equations rather than implications
  because that often simplifies their proof.  Make sure that the right-hand
  side is (in some sense) simpler than the left-hand side.
  \item
  Eventually you need to relate @{text sorted} and @{text tsorted}.  This is
  facilitated by a function @{text ge} on lists (analogously to @{text tge} on
  trees) and the following lemma (that you will need to prove):\\
  @{term[display] "sorted (a@x#b) = (sorted a \<and> sorted b \<and> ge x a
  \<and> le x b)"}
  \end{itemize}
*}

primrec ge :: "nat \<Rightarrow> nat list \<Rightarrow> bool" where
  "ge a []     = True"
| "ge a (x#xs) = (x \<le> a \<and> ge a xs)"

primrec list_of :: "bintree \<Rightarrow> nat list" where
  "list_of Empty          = []"
| "list_of (Node n t1 t2) = list_of t1 @ [n] @ list_of t2"

lemma [simp]: "le x (a@b) = (le x a \<and> le x b)"
  apply (induct_tac a)
  apply auto
done

lemma [simp]: "ge x (a@b) = (ge x a \<and> ge x b)"
  apply (induct_tac a)
  apply auto
done

lemma [simp]:
  "sorted (a@x#b) = (sorted a \<and> sorted b \<and> ge x a \<and> le x b)"
  apply (induct_tac a)
  apply auto
done

lemma [simp]: "ge n (list_of t) = tge n t"
  apply (induct_tac t)
  apply auto
done

lemma [simp]: "le n (list_of t) = tle n t"
  apply (induct_tac t)
  apply auto
done
  
lemma [simp]: "sorted (list_of t) = tsorted t"
  apply (induct_tac t)
  apply auto
done

theorem "sorted (list_of (tree_of xs))"
  by auto

lemma count_append [simp]: "count (a@b) n = count a n + count b n"
  apply (induct a)
  apply auto
done

lemma [simp]: "count (list_of b) n = tcount b n"
  apply (induct b)
  apply auto
done

theorem "count (list_of (tree_of xs)) n = count xs n"    
  apply (induct xs)
  apply auto
done


(*<*) end (*>*)
