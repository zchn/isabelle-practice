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

thm One_nat_def

subsection \<open>Fibonacci numbers\<close>

fun fib :: "nat \<Rightarrow> nat"
  where
    "fib 0 = 0"
  | "fib (Suc 0) = 1"
  | "fib (Suc (Suc x)) = fib x + fib (Suc x)"

lemma [simp]: "fib (Suc n) > 0"
proof (induction "n")
  case 0
  then show ?case by simp
next
  case Suc
  then show ?case by simp
qed

text \<open>Alternative induction rule.\<close>

theorem fib_induct: "P 0 \<Longrightarrow> P 1 \<Longrightarrow> (\<And>n. P (n + 1) \<Longrightarrow> P n \<Longrightarrow> P (n + 2)) \<Longrightarrow> P n"
  for n :: nat
proof (induct n rule: fib.induct)
  case 1
  then show ?case by simp
next
  case 2
  then show ?case by simp
next
  case (3 x)
  then show ?case by simp
qed


subsection \<open>Fib and gcd commute\<close>

text \<open>A few laws taken from @{cite "Concrete-Math"}.\<close>

lemma fib_add: "fib (n + k + 1) = fib (k + 1) * fib (n + 1) + fib k * fib n"
  (is "?P n")
  \<comment> \<open>see @{cite \<open>page 280\<close> "Concrete-Math"}\<close>
proof (induct n rule: fib.induct)
  case 1
  then show ?case by simp
next
  case 2
  then show ?case by simp
next
  case (3 x)
  then show ?case
  proof -
    fix x
    assume a1: "fib (x + k + 1) = fib (k + 1) * fib (x + 1) + fib k * fib x"
    assume a2: "fib (Suc x + k + 1) = fib (k + 1) * fib (Suc x + 1) + fib k * fib (Suc x)"
    have "fib (Suc (Suc x) + k + 1) = fib (x + k + 1) + fib (Suc x + k + 1)" by simp
    hence "\<dots> = fib (k + 1) * fib (x + 1)
                + fib k * fib x
                + fib (k + 1) * fib (Suc x + 1)
                + fib k * fib (Suc x)" using a1 a2 by simp
    hence "fib (Suc (Suc x) + k + 1) = fib (k + 1) * (fib (x + 1) + fib (Suc x + 1))
                                     + fib k * (fib x + fib (Suc x))" by (simp add: add_mult_distrib2)
    thus "fib (Suc (Suc x) + k + 1) = fib (k + 1) * fib (Suc (Suc x) + 1)
                                     + fib k * fib (Suc (Suc x))" by simp
  qed
qed

lemma gcd_fib_Suc_eq_1: "gcd (fib n) (fib (n + 1)) = 1"
  (is "?P n")
proof (induct n rule: fib_induct)
  case 1
  then show ?case by simp
next
  case 2
  then show ?case by simp
next
  case (3 n)
  assume "gcd (fib (n + 1)) (fib (n + 1 + 1)) = 1"
  assume "gcd (fib n) (fib (n + 1)) = 1"
  have "fib (Suc (Suc n) + 1) = fib (n + 1) + fib (Suc n + 1)" by simp
  also have "\<dots> = fib (Suc n + 1) + fib (n + 1)" by simp
  also have "gcd (fib (Suc n + 1)) \<dots> =
             gcd (fib (Suc n + 1)) (fib (n + 1))" by (rule gcd_add2)
  also have "\<dots> = gcd (fib (n + 1)) (fib (Suc n + 1))" by (simp add: gcd.commute)
  finally have *: "\<dots> = gcd (fib (n + 2)) (fib (n + 2 + 1))" by simp
  thus "gcd (fib (n + 2)) (fib (n + 2 + 1)) = 1" using 3 by simp
qed

lemma gcd_mult_add: "(0::nat) < n \<Longrightarrow> gcd (n * k + m) n = gcd m n"
proof -
  assume "(0::nat) < n"
  hence "gcd (n * k + m) n = gcd n (m mod n)"
    by (simp add: gcd_non_0_nat add.commute)
  also from \<open>0 < n\<close> have "\<dots> = gcd m n" by (simp add: gcd_non_0_nat)
  finally show ?thesis .
qed

lemma gcd_fib_add: "gcd (fib m) (fib (n + m)) = gcd (fib m) (fib n)"
proof (cases m)
  case 0
  then show ?thesis by simp
next
  case (Suc k)
  hence "gcd (fib m) (fib (n + m)) = gcd (fib (n + k + 1)) (fib (k + 1))"
    by (simp add: gcd.commute)
  also have "fib (n + k + 1) = fib (k + 1) * fib (n + 1) + fib k * fib n"
    by (rule fib_add)
  also have "gcd \<dots> (fib (k + 1)) = gcd (fib k * fib n) (fib (k + 1))"
    by (simp add: gcd_mult_add)
  also have "\<dots> = gcd (fib n) (fib (k + 1))"
    by (simp only: gcd_fib_Suc_eq_1 gcd_mult_cancel)
  also have "\<dots> = gcd (fib m) (fib n)"
    using Suc by (simp add: gcd.commute)
  finally show ?thesis .
qed

lemma gcd_fib_diff: "gcd (fib m) (fib (n - m)) = gcd (fib m) (fib n)" if "m \<le> n"
  oops

lemma gcd_fib_mod: "gcd (fib m) (fib (n mod m)) = gcd (fib m) (fib n)" if "0 < m"
  oops

theorem fib_gcd: "fib (gcd m n) = gcd (fib m) (fib n)"
  (is "?P m n")
  oops

end
