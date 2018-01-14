theory Exe4p3
  imports Main
begin

inductive ev :: "nat \<Rightarrow> bool" where
ev0: "ev 0" |
evSS : "ev n \<Longrightarrow> ev (Suc(Suc n))"

fun evn :: "nat \<Rightarrow> bool" where
"evn 0 = True" |
"evn (Suc 0) = False" |
"evn (Suc(Suc n)) = evn n"

lemma "ev (Suc m) \<Longrightarrow> \<not> ev m"
proof (induction "Suc m" arbitrary: m rule: ev.induct)
  fix n assume IH: "\<And>m. n = Suc m \<Longrightarrow> \<not>ev m"
  show "\<not>ev (Suc n)"
  proof
    assume "ev(Suc n)"
    thus False
    proof cases
      fix k assume "n = Suc k" "ev k"
      thus False using IH by auto
    qed
  qed
qed

lemma assumes a: "ev(Suc(Suc n))" shows "ev n"
proof -
  have "ev(Suc(Suc n)) \<Longrightarrow> ev n"
  proof (induction "Suc(Suc n)" arbitrary: n rule: ev.induct)
    case ev0
    fix n assume "ev n"
    thus "ev n" by simp
  qed
  thus ?thesis using a by simp
qed

end
