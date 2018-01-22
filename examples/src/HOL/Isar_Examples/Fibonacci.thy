(*  Title:      HOL/Isar_Examples/Fibonacci.thy
    Author:     Gertrud Bauer
    Copyright   1999 Technische Universitaet Muenchen

The Fibonacci function.  Original
tactic script by Lawrence C Paulson.

Fibonacci numbers: proofs of laws taken from

  R. L. Graham, D. E. Knuth, O. Patashnik.
  Concrete Mathematics.
  (Addison-Wesley, 1989)
*)

section \<open>Fib and Gcd commute\<close>

theory Fibonacci
  imports "HOL-Computational_Algebra.Primes"
begin

text_raw \<open>\<^footnote>\<open>Isar version by Gertrud Bauer. Original tactic script by Larry
  Paulson. A few proofs of laws taken from @{cite "Concrete-Math"}.\<close>\<close>


declare One_nat_def [simp]


subsection \<open>Fibonacci numbers\<close>

fun fib :: "nat \<Rightarrow> nat"
  where
    "fib 0 = 0"
  | "fib (Suc 0) = 1"
  | "fib (Suc (Suc x)) = fib x + fib (Suc x)"

lemma [simp]: "fib (Suc n) > 0"
  oops


text \<open>Alternative induction rule.\<close>

theorem fib_induct: "P 0 \<Longrightarrow> P 1 \<Longrightarrow> (\<And>n. P (n + 1) \<Longrightarrow> P n \<Longrightarrow> P (n + 2)) \<Longrightarrow> P n"
  oops


subsection \<open>Fib and gcd commute\<close>

text \<open>A few laws taken from @{cite "Concrete-Math"}.\<close>

lemma fib_add: "fib (n + k + 1) = fib (k + 1) * fib (n + 1) + fib k * fib n"
  (is "?P n")
  \<comment> \<open>see @{cite \<open>page 280\<close> "Concrete-Math"}\<close>
  oops

lemma gcd_fib_Suc_eq_1: "gcd (fib n) (fib (n + 1)) = 1"
  (is "?P n")
  oops

lemma gcd_mult_add: "(0::nat) < n \<Longrightarrow> gcd (n * k + m) n = gcd m n"
  oops
  
lemma gcd_fib_add: "gcd (fib m) (fib (n + m)) = gcd (fib m) (fib n)"
  oops

lemma gcd_fib_diff: "gcd (fib m) (fib (n - m)) = gcd (fib m) (fib n)" if "m \<le> n"
  oops

lemma gcd_fib_mod: "gcd (fib m) (fib (n mod m)) = gcd (fib m) (fib n)" if "0 < m"
  oops

theorem fib_gcd: "fib (gcd m n) = gcd (fib m) (fib n)"
  (is "?P m n")
  oops

end
