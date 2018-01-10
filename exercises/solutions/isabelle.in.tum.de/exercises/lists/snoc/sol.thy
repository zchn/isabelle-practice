(*
    $Id: sol.thy,v 1.3 2011/06/28 18:11:38 webertj Exp $
    Author: Tjark Weber
*)

header {* SNOC *}

(*<*) theory sol imports Main begin (*>*)

text {*
Define a primitive recursive function @{text snoc} that appends an element
at the \emph{right} end of a list. Do not use @{text"@"} itself.
*}

primrec snoc :: "'a list => 'a => 'a list" where
  "snoc []     a = [a]"
| "snoc (x#xs) a = x # snoc xs a"

lemma snoc_append: "snoc xs a = xs @ [a]"
  apply (induct "xs")
  apply auto
done

text {*
Prove the following theorem:
*}

theorem rev_cons: "\<forall>x. rev (x # xs) = snoc (rev xs) x"
  apply (induct "xs")
  apply (auto simp add: snoc_append)
done

text {*
Hint: you need to prove a suitable lemma first.
*}

(*<*) end (*>*)
