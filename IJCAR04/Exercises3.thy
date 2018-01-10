theory Exercises3 imports Main begin

text {* Solve in Isar. *}

lemma "\<exists>x. \<forall>y. P x y \<Longrightarrow> \<forall>y. \<exists>x. P x y"
oops


text {* Tricky *}
lemma "\<exists>x. P x \<longrightarrow> (\<forall>x. P x)"
oops

text {* Prove using moreover/ultimately. *}

declare ring_eq_simps [simp]

text {* 
  you may need to use (simp del: right_diff_distrib) 
  in the following proof 
*}

lemma dvd_minus:
  assumes du: "(d::int) dvd u"
  assumes dv: "d dvd v"
  shows  "d dvd u - v"
oops

text {* Prove using also/finally. *}

lemma "(x+y::int)*(x-y) = x*x - y*y"
oops

text {* Define locales for partial orders and semi-lattices.
  Use the order relation @{text \<sqsubseteq>}. *}

locale order

locale partial_order

text {* In order to avoid choice operators, use a predicate for infimum. *}

locale inf

text {* Show that infimum is unique and associative. *}

text {* In a second variant, without syntax, define lattice using two
  semi-lattices. *}

text {* Hint: in order to avoid duplicate parameters, import the
  predefined locale "var x" instead of using "fixes x". *}

locale partial_order'

locale inf'

locale rev_order'

locale sup'

locale lattice

end
