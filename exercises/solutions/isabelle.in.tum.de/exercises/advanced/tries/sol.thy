(*  
    $Id: sol.thy,v 1.4 2011/06/28 18:11:37 webertj Exp $
    Author: Tobias Nipkow
*)

header {* Tries *}

(*<*) theory sol imports Main begin (*>*)

text {*
  Section~3.4.4 of the Isabelle/HOL tutorial is a case study about so-called
  \emph{tries}, a data structure for fast indexing with strings.  Read that
  section.

  The data type of tries over the alphabet type @{typ 'a} und the value type
  @{typ 'v} is defined as follows:
*}

datatype ('a, 'v) trie = Trie "'v option" "('a * ('a,'v) trie) list"

text {*
  A trie consists of an optional value and an association list that maps
  letters of the alphabet to subtrees.  Type @{typ "'a option"} is defined in
  Section~2.5.3 of the Isabelle/HOL tutorial.

  There are also two selector functions @{term value} and @{term alist}:
*}

primrec "value" :: "('a, 'v) trie \<Rightarrow> 'v option" where
"value (Trie ov al) = ov"

primrec alist :: "('a, 'v) trie \<Rightarrow> ('a * ('a,'v) trie) list" where
"alist (Trie ov al) = al"

text {*
  Furthermore there is a function @{term lookup} on tries defined with the help
  of the generic search function @{term assoc} on association lists:
*}

primrec assoc ::  "('key * 'val)list \<Rightarrow> 'key \<Rightarrow> 'val option" where
  "assoc []     x = None"
| "assoc (p#ps) x =
           (let (a, b) = p in if a = x then Some b else assoc ps x)"

primrec lookup :: "('a, 'v) trie \<Rightarrow> 'a list \<Rightarrow> 'v option" where
  "lookup t []     = value t"
| "lookup t (a#as) = (case assoc (alist t) a of
                          None \<Rightarrow> None
                        | Some at \<Rightarrow> lookup at as)"

text {*
  Finally, @{term update} updates the value associated with some string with a
  new value, overwriting the old one:
*}

primrec update :: "('a, 'v) trie \<Rightarrow> 'a list \<Rightarrow> 'v \<Rightarrow> ('a, 'v) trie" where
  "update t []     v = Trie (Some v) (alist t)"
| "update t (a#as) v =
     (let tt = (case assoc (alist t) a of
                  None \<Rightarrow> Trie None [] 
                | Some at \<Rightarrow> at)
      in Trie (value t) ((a, update tt as v) # alist t))"

text {*
  The following theorem tells us that @{term update} behaves as expected:
*}

lemma [simp]: "lookup (Trie None []) as = None"
  by (case_tac as, simp_all)

declare Let_def[simp] option.split[split]

theorem [simp]: "\<forall>t v bs. lookup (update t as v) bs =
                    (if as = bs then Some v else lookup t bs)"
  apply (induct_tac as, auto)
  apply (case_tac[!] bs, auto)
done


text {*
  As a warm-up exercise, define a function

  @{text "modify :: ('a, 'v) trie \<Rightarrow> 'a list \<Rightarrow> 'v option \<Rightarrow> ('a, 'v) trie"}

  for inserting as well as deleting elements from a trie.  Show that @{term
  modify} satisfies a suitably modified version of the correctness theorem for
  @{term update}.
*}

primrec modify :: "('a, 'v) trie \<Rightarrow> 'a list \<Rightarrow> 'v option \<Rightarrow> ('a, 'v) trie" where
  "modify t []     vo = Trie vo (alist t)"
| "modify t (a#as) vo =
     (let tt = (case assoc (alist t) a of
                  None \<Rightarrow> Trie None [] 
                | Some at \<Rightarrow> at)
      in Trie (value t) ((a, modify tt as vo) # alist t))"

theorem [simp]: "\<forall>t v bs. lookup (modify t as v) bs =
                    (if as = bs then v else lookup t bs)"
  apply (induct_tac as, auto)
  apply (case_tac[!] bs, auto)
done


text {*
  The above definition of @{term update} has the disadvantage that it often
  creates junk: each association list it passes through is extended at the left
  end with a new (letter,value) pair without removing any old association of
  that letter which may already be present.  Logically, such cleaning up is
  unnecessary because @{term assoc} always searches the list from the left.
  However, it constitutes a space leak: the old associations cannot be garbage
  collected because physically they are still reachable.  This problem can be
  solved by means of a function

  @{text "overwrite :: 'a \<Rightarrow> 'b \<Rightarrow> ('a * 'b) list \<Rightarrow> ('a * 'b) list"}

  that does not just add new pairs at the front but replaces old associations
  by new pairs if possible.

  Define @{term overwrite}, modify @{term modify} to employ @{term overwrite},
  and show the same relationship between @{term modify} and @{term lookup} as
  before.
*}

primrec overwrite :: "'a \<Rightarrow> 'b \<Rightarrow> ('a * 'b) list \<Rightarrow> ('a * 'b) list" where
  "overwrite a v []     = [(a,v)]"
| "overwrite a v (p#ps) = (let (b, u ) = p in (if a=b then (a,v)#ps else (b,u) # overwrite a v ps))"

lemma [simp]: "\<forall> a v b. assoc (overwrite a v ps) b = assoc ((a,v)#ps) b"
  by (induct_tac ps, auto)

primrec modify2 :: "('a, 'v) trie \<Rightarrow> 'a list \<Rightarrow> 'v option \<Rightarrow> ('a, 'v) trie" where
  "modify2 t []     vo = Trie vo (alist t)"
| "modify2 t (a#as) vo =
     (let tt = (case assoc (alist t) a of 
                  None \<Rightarrow> Trie None []  
                | Some at \<Rightarrow> at) 
      in Trie (value t) (overwrite a (modify2 tt as vo) (alist t)))"

theorem "\<forall>t v bs. lookup (modify2 t as vo) bs =
                    (if as = bs then vo else lookup t bs)"
  apply (induct_tac as, auto)
  apply (case_tac[!] bs, auto)
done


text {*
  Instead of association lists we can also use partial functions that map
  letters to subtrees.  Partiality can be modelled with the help of type @{typ
  "'a option"}: if @{term f} is a function of type \mbox{@{typ "'a
  \<Rightarrow> 'b option"}}, let @{term "f a = Some b"} if @{term a} should be
  mapped to some @{term b}, and let @{term "f a = None"} otherwise.
*}

datatype ('a, 'v) trieP = TrieP "'v option" "'a \<Rightarrow> ('a,'v) trieP option"

text {*
  Modify the definitions of @{term lookup} and @{term modify} accordingly and
  show the same correctness theorem as above.
*}

primrec value3 :: "('a, 'v) trieP \<Rightarrow> 'v option" where
"value3 (TrieP ov m) = ov"

primrec mapping3 :: "('a,'v) trieP \<Rightarrow> 'a \<Rightarrow> ('a, 'v) trieP option" where
"mapping3 (TrieP ov m) = m"

primrec lookup3 :: "('a,'v) trieP \<Rightarrow> 'a list \<Rightarrow> 'v option" where
  "lookup3 t [] = value3 t"
| "lookup3 t (a#as) = (case mapping3 t a of
                        None \<Rightarrow> None
                      | Some at \<Rightarrow> lookup3 at as)"

lemma [simp]: "lookup3 (TrieP None (\<lambda>c. None)) as = None"
  by (case_tac as, simp_all)

primrec modify3 :: "('a,'v) trieP \<Rightarrow> 'a list \<Rightarrow> 'v option \<Rightarrow> ('a,'v) trieP" where
  "modify3 t []     vo = TrieP vo (mapping3 t)"
| "modify3 t (a#as) vo =
     (let tt = (case mapping3 t a of
                  None \<Rightarrow> TrieP None (\<lambda>c. None) 
                | Some at \<Rightarrow> at)
      in TrieP (value3 t) 
              (\<lambda>c. if c = a then Some (modify3 tt as vo) else mapping3 t c))"

theorem "\<forall>t v bs. lookup3 (modify3 t as vo) bs = 
                    (if as = bs then vo else lookup3 t bs)"
  apply (induct_tac as, auto)
  apply (case_tac[!] bs, auto)
done


(*<*) end (*>*)
