(*  Title:      HOL/Isar_Examples/Cantor.thy
    Author:     Makarius
*)

section \<open>Cantor's Theorem\<close>

theory Cantor
  imports Main
begin

subsection \<open>Mathematical statement and proof\<close>

text \<open>
  Cantor's Theorem states that there is no surjection from
  a set to its powerset.  The proof works by diagonalization.  E.g.\ see
  \<^item> \<^url>\<open>http://mathworld.wolfram.com/CantorDiagonalMethod.html\<close>
  \<^item> \<^url>\<open>https://en.wikipedia.org/wiki/Cantor's_diagonal_argument\<close>
\<close>

theorem Cantor: "\<nexists>f :: 'a \<Rightarrow> 'a set. \<forall>A. \<exists>x. A = f x"
  oops

subsection \<open>Automated proofs\<close>

text \<open>
  These automated proofs are much shorter, but lack information why and how it
  works.
\<close>

theorem "\<nexists>f :: 'a \<Rightarrow> 'a set. \<forall>A. \<exists>x. f x = A"
  oops

theorem "\<nexists>f :: 'a \<Rightarrow> 'a set. \<forall>A. \<exists>x. f x = A"
  oops


subsection \<open>Elementary version in higher-order predicate logic\<close>

text \<open>
  The subsequent formulation bypasses set notation of HOL; it uses elementary
  \<open>\<lambda>\<close>-calculus and predicate logic, with standard introduction and elimination
  rules. This also shows that the proof does not require classical reasoning.
\<close>

lemma iff_contradiction:
  assumes *: "\<not> A \<longleftrightarrow> A"
  shows False
  oops
  
theorem Cantor': "\<nexists>f :: 'a \<Rightarrow> 'a \<Rightarrow> bool. \<forall>A. \<exists>x. A = f x"
  oops

subsection \<open>Classic Isabelle/HOL example\<close>

text \<open>
  The following treatment of Cantor's Theorem follows the classic example from
  the early 1990s, e.g.\ see the file @{verbatim "92/HOL/ex/set.ML"} in
  Isabelle92 or @{cite \<open>\S18.7\<close> "paulson-isa-book"}. The old tactic scripts
  synthesize key information of the proof by refinement of schematic goal
  states. In contrast, the Isar proof needs to say explicitly what is proven.

  \<^bigskip>
  Cantor's Theorem states that every set has more subsets than it has
  elements. It has become a favourite basic example in pure higher-order logic
  since it is so easily expressed:

  @{text [display]
  \<open>\<forall>f::\<alpha> \<Rightarrow> \<alpha> \<Rightarrow> bool. \<exists>S::\<alpha> \<Rightarrow> bool. \<forall>x::\<alpha>. f x \<noteq> S\<close>}

  Viewing types as sets, \<open>\<alpha> \<Rightarrow> bool\<close> represents the powerset of \<open>\<alpha>\<close>. This
  version of the theorem states that for every function from \<open>\<alpha>\<close> to its
  powerset, some subset is outside its range. The Isabelle/Isar proofs below
  uses HOL's set theory, with the type \<open>\<alpha> set\<close> and the operator \<open>range :: (\<alpha> \<Rightarrow>
  \<beta>) \<Rightarrow> \<beta> set\<close>.
\<close>

theorem "\<exists>S. S \<notin> range (f :: 'a \<Rightarrow> 'a set)"
  oops
  
text \<open>
  How much creativity is required? As it happens, Isabelle can prove this
  theorem automatically using best-first search. Depth-first search would
  diverge, but best-first search successfully navigates through the large
  search space. The context of Isabelle's classical prover contains rules for
  the relevant constructs of HOL's set theory.
\<close>

theorem "\<exists>S. S \<notin> range (f :: 'a \<Rightarrow> 'a set)"
  oops

end
