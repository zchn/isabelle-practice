theory Exe4p5
  imports Main
begin

inductive ev :: "nat \<Rightarrow> bool" where
ev0: "ev 0" |
evSS : "ev n \<Longrightarrow> ev (Suc(Suc n))"

fun evn :: "nat \<Rightarrow> bool" where
"evn 0 = True" |
"evn (Suc 0) = False" |
"evn (Suc(Suc n)) = evn n"

lemma "\<not>ev(Suc(Suc(Suc 0)))"
proof 
  assume "ev(Suc(Suc(Suc 0)))"
  thus "False"
  proof (induction "Suc(Suc(Suc 0))" rule: ev.induct)
    assume "ev(Suc 0)"
    thus "False"
    proof (induction "Suc 0" rule: ev.induct)
    qed
  qed
qed
