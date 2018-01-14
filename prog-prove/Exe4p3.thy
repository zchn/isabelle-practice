theory Exe4p3
  imports Main
begin

inductive ev :: "nat \<Rightarrow> bool" where
ev0: "ev 0" |
evSS: "ev n \<Longrightarrow> ev(Suc(Suc n))"

fun evn :: "nat \<Rightarrow> bool" where
"evn 0 = True" |
"evn (Suc 0) = False" | 
"evn (Suc (Suc n)) = evn n"

lemma fixes a b :: int assumes "b dvd (a+b)" shows "b dvd a"
proof -
  { fix k assume kk: "a+b = b*k"
    have "\<exists>k'. a = b*k'"
    proof
      show "a=b*(k-1)" using kk by (simp add: algebra_simps)
    qed }
  then show ?thesis using assms by (auto simp add: dvd_def)
qed

lemma fixes n :: nat assumes "ev n" shows "evn n"
proof -
  have "ev n \<Longrightarrow> evn n"
  proof (induction rule: ev.induct)
    case ev0
    then show ?case by auto
  next
    case (evSS n)
    then show ?case by auto
  qed
  thus "evn n" using assms by simp
qed

lemma "ev n \<Longrightarrow> ev (n-2)"
proof -
  assume "ev n"
  from this have "ev (n-2)"
  proof cases
    case ev0
    then show ?thesis by (simp add: ev.ev0)
  next
    case (evSS n)
    then show ?thesis by (simp add: ev.evSS)
  qed
  thus ?thesis by simp
qed

lemma "ev(Suc(Suc n)) \<Longrightarrow> ev n"
proof -
  assume "ev(Suc(Suc n))"
  from this have "ev n"
  proof cases
    case ev0
    then show ?thesis by auto
next
  case evSS
  then show ?thesis sorry
qed
