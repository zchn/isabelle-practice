(*
    $Id: ex.thy,v 1.2 2004/11/23 15:14:34 webertj Exp $
*)

header {* A Riddle: Rich Grandfather *}

(*<*) theory ex imports Main begin (*>*)

text {*
  First prove the following formula, which is valid in classical predicate
  logic, informally with pen and paper.  Use case distinctions and/or proof by
  contradiction.

  {\it  If every poor man has a rich father,\\
   then there is a rich man who has a rich grandfather.}
*}

theorem
  "\<forall>x. \<not> rich x \<longrightarrow> rich (father x) \<Longrightarrow>
  \<exists>x. rich (father (father x)) \<and> rich x" (*<*) oops (*>*)

text {*
  Now prove the formula in Isabelle using a sequence of rule applications (i.e.\
  only using the methods @{term rule}, @{term erule} and @{term assumption}).
*}

(*<*) end (*>*)
