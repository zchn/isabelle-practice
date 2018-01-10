(*
    $Id: sol.thy,v 1.4 2011/06/28 18:11:38 webertj Exp $
*)

header {* Sum of List Elements, Tail-Recursively *}

(*<*) theory sol imports Main begin (*>*)

text {*
\begin{description}
\item[\bf (a)] Define a primitive recursive function @{term ListSum} that
computes the sum of all elements of a list of natural numbers.

Prove the following equations.  Note that @{term  "[0..n]"} und @{term
"replicate n a"} are already defined in a theory {\tt List.thy}.
\end{description}
*}

  primrec ListSum :: "nat list \<Rightarrow> nat" where 
    "ListSum []     = 0"
  | "ListSum (x#xs) = x + ListSum xs"

  theorem ListSum_append[simp]: "ListSum (xs @ ys) = ListSum xs + ListSum ys"
    apply (induct xs)
    apply auto
  done

  theorem "2 * ListSum [0..<n+1] = n * (n + 1)"
    apply (induct n)
    apply auto
  done

  theorem "ListSum (replicate n a) = n * a"
    apply (induct n)
    apply auto
  done


text {* 
\begin{description}
\item[\bf (b)] Define an equivalent function @{term ListSumT} using a
tail-recursive function @{term ListSumTAux}.  Prove that @{term ListSum}
and @{term ListSumT} are in fact equivalent.
\end{description}
*}

  primrec ListSumTAux :: "nat list \<Rightarrow> nat \<Rightarrow> nat" where
    "ListSumTAux []     n = n"
  | "ListSumTAux (x#xs) n = ListSumTAux xs (x + n)"

  definition ListSumT :: "nat list \<Rightarrow> nat" where
    "ListSumT xs == ListSumTAux xs 0"

  lemma ListSumTAux_add [rule_format]: "\<forall>a b. ListSumTAux xs (a+b) = a + ListSumTAux xs b"
    apply (induct xs)
    apply auto
  done

  lemma [simp]: "ListSumT [] = 0"
    by (auto simp add: ListSumT_def)

  lemma [simp]: "ListSumT (x#xs) = x + ListSumT xs"
    by (auto simp add: ListSumT_def ListSumTAux_add[THEN sym])

  theorem "ListSumT xs = ListSum xs"
    apply (induct xs)
    apply auto
  done

(*<*) end (*>*)
