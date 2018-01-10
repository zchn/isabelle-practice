(*
    $Id: ex.thy,v 1.2 2004/11/23 15:14:34 webertj Exp $
    Author: Martin Strecker
*)

header {* Elimination of Connectives *}

(*<*) theory ex imports Main begin (*>*)

text {* In classical propositional logic, the connectives @{text "=, \<or>,
\<not>"} can be replaced by @{text "\<longrightarrow>, \<and>, False"}.  Define
corresponding simplification rules as lemmas and prove their correctness.  (You
may use automated proof tactics.) *}


text {* What is the result of your translation for the formula @{text "A \<or>
(B \<and> C) = A"}?  (You can use Isabelle's simplifier to compute the result
by using the simplifier's @{text "only"} option.) *}


(*<*) end (*>*)
