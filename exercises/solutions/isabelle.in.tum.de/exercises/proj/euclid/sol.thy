(*
    $Id: sol.thy,v 1.4 2010/11/29 07:13:36 kleing Exp $
    Author: Martin Strecker
*)

header {* The Euclidean Algorithm -- Inductively *}

(*<*) theory sol imports Main begin (*>*)

subsection {* Rules without base case *}

text {* Show that the following *}

inductive_set evenempty :: "nat set" where
Add2Ie: "n \<in> evenempty \<Longrightarrow> Suc(Suc n) \<in> evenempty"

text {* defines the empty set: *}

lemma evenempty_empty: "evenempty = {}"
by (auto elim: evenempty.induct)


subsection {* The Euclidean algorithm *}

text {* Define inductively the set @{text gcd}:
@{text "(a,b,g) \<in> gcd"} means that @{text g} is the greatest common divisor
of @{text a} und @{text b}. The definition should closely follow the
Euclidean algorithm.

Reminder: The Euclidean algorithm repeatedly subtracts the smaller
from the larger number, until one of the numbers is 0. Then, the other
number is the gcd. *}

inductive_set  gcd :: "(nat \<times> nat \<times> nat) set" where
gcdZero: "(u, 0, u) \<in> gcd" |
gcdStep: "\<lbrakk> (u - v, v, g) \<in> gcd; 0 < v; v \<le> u \<rbrakk> \<Longrightarrow> (u, v, g) \<in> gcd" |
gcdSwap: "\<lbrakk> (v, u, g) \<in> gcd; u < v \<rbrakk> \<Longrightarrow> (u, v, g) \<in> gcd"


text {* Now, compute the gcd of 15 and 10: *}

schematic_lemma "(15, 10, ?g)  \<in> gcd"
  apply (rule gcdStep) apply simp
  apply (rule gcdSwap) 
  apply (rule gcdStep) apply simp
  apply (rule gcdStep) apply simp
  apply (rule gcdSwap)
  apply (rule gcdZero)
  apply simp+
done


text {* How does your algorithm behave on special cases as the following? *}

schematic_lemma "(0, 0, ?g)  \<in> gcd"
by (rule gcdZero)


text {* Show that the gcd is really a divisor (for the proof, you need an
appropriate lemma): *}

lemma gcd_divides: "(a,b,g) \<in> gcd \<Longrightarrow> g dvd a \<and> g dvd b"
(*<*) oops (*>*)

lemma dvd_minus: "\<lbrakk> v \<le> u;  (g::nat) dvd u - v; g dvd v\<rbrakk> \<Longrightarrow> g dvd u"
  apply (clarsimp simp add: dvd_def)
  apply (rule_tac x="k + ka" in exI)
  apply (simp add: add_mult_distrib2)
done

lemma gcd_divides: "(a,b,g) \<in> gcd \<Longrightarrow> g dvd a \<and> g dvd b"
  apply (induct rule: gcd.induct)
  apply simp
  apply (simp add: dvd_minus)
  apply simp
done


text {* Show that the gcd is the greatest common divisor: *}

lemma gcd_greatest [rule_format]: "(a,b,g) \<in> gcd \<Longrightarrow>
  0 < a \<or> 0 < b \<longrightarrow> (\<forall> d. d dvd a \<longrightarrow> d dvd b \<longrightarrow> d \<le> g)"
(*<*) oops (*>*)

lemma dvd_leq: "\<lbrakk> 0 < v; (d\<Colon>nat) dvd v \<rbrakk> \<Longrightarrow> d \<le> v"
  by (clarsimp simp add: dvd_def)

lemma dvd_minus2: "\<lbrakk> (d::nat) dvd u; d dvd v \<rbrakk> \<Longrightarrow> d dvd u - v"
  apply (clarsimp simp add: dvd_def)
  apply (rule_tac x="k-ka" in exI)
  apply (simp add: diff_mult_distrib2)
done

lemma gcd_greatest [rule_format]: "(a,b,g) \<in> gcd \<Longrightarrow>
  0 < a \<or> 0 < b \<longrightarrow> (\<forall> d. d dvd a \<longrightarrow> d dvd b \<longrightarrow> d \<le> g)"
  apply (induct rule: gcd.induct)
  apply (clarsimp simp add: dvd_leq)

  apply clarsimp
  apply (case_tac "v = u")
  apply simp
  apply (blast dest: dvd_minus2)+
done


text {* Here as well, you will have to prove a suitable lemma. What is the
precondition @{text "0 < a \<or> 0 < b"} good for?

So far, we have only shown that @{text gcd} is correct, but your algorithm
might not compute a result for all values @{text "a,b"}.  Thus, show
completeness of the algorithm: *}

lemma gcd_defined: "\<forall> a b. \<exists> g. (a, b, g) \<in> gcd"
(*<*) oops (*>*)

text {* The following lemma, proved by course-of-value recursion over @{text
n}, may be useful.  Why does standard induction over natural numbers not work
here? *}

lemma gcd_defined_aux [rule_format]: 
  "\<forall> a b. (a + b) \<le> n \<longrightarrow> (\<exists> g. (a, b, g) \<in> gcd)"
  apply (induct rule: nat_less_induct)
  apply clarify
(*<*) oops (*>*)

text {* The idea is to show that @{text gcd} yields a result for all @{text "a,
b"} whenever it is known that @{text gcd} yields a result for all @{text "a',
b'"} whose sum is smaller than @{text "a + b"}.

In order to prove this lemma, make case distinctions corresponding to the
different clauses of the algorithm, and show how to reduce computation of
@{text gcd} for @{text "a, b"} to computation of @{text gcd} for suitable
smaller @{text "a', b'"}. *}

lemma gcd_defined_aux [rule_format]: 
  "\<forall> a b. (a + b) \<le> n \<longrightarrow> (\<exists> g. (a, b, g) \<in> gcd)"
apply (induct rule: nat_less_induct)
apply clarify

apply (case_tac b)

-- "Application of gcdZero"
apply simp
apply (rule exI)
apply (rule gcdZero)

apply (rename_tac n a b b')
apply simp

apply (case_tac "b \<le> a")

-- "Application of gcdStep"
apply simp
apply (drule_tac x=a in spec, drule mp) 
apply arith
apply (elim allE impE)
prefer 2
apply (elim exE)
apply (rule exI)
apply (rule gcdStep, assumption)
apply simp+

apply (case_tac a)
apply simp

-- "Application of gcdSwap, followed by gcdZero"
apply (drule_tac x=0 in spec, drule mp) apply arith
apply (drule_tac x=0 in spec, drule_tac x=0 in spec, drule mp) 
apply simp
apply (elim exE)
apply (rule exI)
apply (rule gcdSwap) apply (rule gcdZero)
apply simp

-- "Application of gcdSwap, followed by gcdStep"
apply (drule_tac x=b in spec, drule mp) apply arith
apply (elim allE impE)
prefer 2
apply (elim exE)
apply (rule exI)
apply (rule gcdSwap) 
apply (rule gcdStep) apply assumption
apply arith+
done

lemma gcd_defined: "\<forall> a b. \<exists> g. (a, b, g) \<in> gcd"
  apply clarify
  apply (rule_tac n="a + b" in gcd_defined_aux)
  apply simp
done


(*<*) end (*>*)
