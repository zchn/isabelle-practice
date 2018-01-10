(*
    $Id: ex.thy,v 1.4 2012/01/04 14:12:56 webertj Exp $
    Author: Farhad Mehta
*)

header {* Counting Occurrences *}

(*<*) theory ex imports Main begin (*>*)

text{*
Define a function @{term occurs}, such that @{term"occurs x xs"} is
the number of occurrences of the element @{term x} in the list @{term
xs}.
*}

(*<*)consts(*>*)  occurs :: "'a \<Rightarrow> 'a list \<Rightarrow> nat"


text {*
Prove (or let Isabelle disprove) the lemmas that follow. You may have
to prove additional lemmas first.  Use the @{text "[simp]"}-attribute
only if the equation is truly a simplification and is necessary for
some later proof.
*}

lemma "occurs a xs = occurs a (rev xs)"
(*<*)oops(*>*)

lemma "occurs a xs <= length xs"
(*<*)oops(*>*)


text{* Function @{text map} applies a function to all elements of a list:
@{text"map f [x\<^isub>1,\<dots>,x\<^isub>n] = [f x\<^isub>1,\<dots>,f x\<^isub>n]"}. *}

lemma "occurs a (map f xs) = occurs (f a) xs"
(*<*)oops(*>*)

text{*
Function @{text"filter :: ('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list"} is defined
by @{thm[display]filter.simps[no_vars]} Find an expression @{text e}
not containing @{text filter} such that the following becomes a true
lemma, and prove it:
*}

lemma "occurs a (filter P xs) = e"
(*<*)oops(*>*)


text{*
With the help of @{term occurs}, define a function @{term remDups}
that removes all duplicates from a list.
*}

(*<*)consts(*>*)  remDups :: "'a list \<Rightarrow> 'a list"


text{*
Find an expression @{text e} not containing @{text remDups} such that
the following becomes a true lemma, and prove it:
*}

lemma "occurs x (remDups xs) = e"
(*<*)oops(*>*)


text{*
With the help of @{term occurs} define a function @{term unique}, such
that @{term "unique xs"} is true iff every element in @{term xs}
occurs only once.
*}

(*<*)consts(*>*)  unique :: "'a list \<Rightarrow> bool"


text{* Show that the result of @{term remDups} is @{term unique}. *}


(*<*) end (*>*)
