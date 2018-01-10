(*
    $Id: ex.thy,v 1.3 2008/07/04 15:37:21 nipkow Exp $
*)

header {* Sum of List Elements, Tail-Recursively *}

(*<*) theory ex imports Main begin (*>*)

text {*
\begin{description}
\item[\bf (a)] Define a primitive recursive function @{term ListSum} that
computes the sum of all elements of a list of natural numbers.

Prove the following equations.  Note that @{term  "[0..n]"} und @{term
"replicate n a"} are already defined in a theory {\tt List.thy}.
\end{description}
*}

  consts ListSum :: "nat list \<Rightarrow> nat"

  theorem "2 * ListSum [0..<n+1] = n * (n + 1)" (*<*) oops (*>*)

  theorem "ListSum (replicate n a) = n * a" (*<*) oops (*>*)


text {* 
\begin{description}
\item[\bf (b)] Define an equivalent function @{term ListSumT} using a
tail-recursive function @{term ListSumTAux}.  Prove that @{term ListSum}
and @{term ListSumT} are in fact equivalent.
\end{description}
*}

  consts ListSumTAux :: "nat list \<Rightarrow> nat \<Rightarrow> nat"

  consts ListSumT :: "nat list \<Rightarrow> nat"

  theorem "ListSum xs = ListSumT xs" (*<*) oops (*>*)

(*<*) end (*>*)
