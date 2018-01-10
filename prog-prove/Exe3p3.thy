theory Exe3p3
  imports Main
begin

inductive star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
refl: "star r x x" |
step: "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

lemma star_post: "star r x y \<Longrightarrow> r y z \<Longrightarrow> star r x z"
  apply(induction rule: star.induct)
   apply(auto simp add: refl step)
  done

lemma star_trans: "star r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"
  apply(induction rule: star.induct)
   apply(auto simp add: step)
  done

inductive star' :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
refl': "star' r x x" |
step': "star' r x y \<Longrightarrow> r y z \<Longrightarrow> star' r x z"

lemma "star' r x y \<Longrightarrow> star r x y"
  apply(induction rule: star'.induct)
   apply(auto simp add: refl step star_post)
  done

thm step'

lemma star'_one: "r x y \<Longrightarrow> star' r x y"
  apply(rule step'[where ?y = "x" and ?z = "y"])
  by (auto simp add: refl')

lemma "star' r xa y \<Longrightarrow>
       r y z \<Longrightarrow>
       (r x xa \<Longrightarrow> star' r x y) \<Longrightarrow> r x xa \<Longrightarrow> star' r x z"
  apply(induction rule: star'.induct)
   apply(auto simp add: refl' step')
  done

lemma star'_pre: "r x y \<Longrightarrow> star' r y z \<Longrightarrow> star' r x z"
  oops
  

lemma star'_trans: "star' r x y \<Longrightarrow> star' r y z \<Longrightarrow> star' r x z"
  apply(induction rule: star'.induct)
   apply(assumption)
  oops

lemma "star r x y \<Longrightarrow> star' r x y"
  apply(induction rule: star.induct)
   apply(auto simp add: refl' step')
  oops

end