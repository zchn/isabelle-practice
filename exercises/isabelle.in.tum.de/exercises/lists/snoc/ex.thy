(*
    $Id: ex.thy,v 1.2 2004/11/23 15:14:34 webertj Exp $
*)

header {* SNOC *}

(*<*) theory ex imports Main begin (*>*)

text {*
Define a primitive recursive function @{text snoc} that appends an element
at the \emph{right} end of a list. Do not use @{text"@"} itself.
*}

consts
  snoc :: "'a list => 'a => 'a list"

text {*
Prove the following theorem:
*}

theorem rev_cons: "rev (x # xs) = snoc (rev xs) x"
(*<*)oops(*>*)

text {*
Hint: you need to prove a suitable lemma first.
*}

(*<*) end (*>*)
