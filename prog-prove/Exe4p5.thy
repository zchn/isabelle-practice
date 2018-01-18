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

inductive star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
refl: "star r x x" |
step: "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

inductive iter :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
iter_refl: "iter r 0 x x" |
iter_step: "r x y \<Longrightarrow> iter r n y z \<Longrightarrow> iter r (Suc n) x z"

lemma fixes r n x y
  assumes s: "iter r n x y"
  shows "star r x y"
proof -
  have "iter r n x y \<Longrightarrow> star r x y"
  proof (induction rule: iter.induct)
    case (iter_refl r x)
    then show ?case by (simp add: star.refl)
  next
    case (iter_step r x y n z)
    then show ?case by (simp add: star.step)
  qed
  thus ?thesis using s by simp
qed
