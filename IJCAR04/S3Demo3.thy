theory Demo3 imports Main begin

section {* Example 1 *}

locale semi =
  fixes prod :: "['a, 'a] => 'a" (infixl "\<cdot>" 70)
  assumes assoc: "(x \<cdot> y) \<cdot> z = x \<cdot> (y \<cdot> z)"

locale group = semi +
  fixes one and inv
  assumes l_one: "one \<cdot> x = x"
    and r_one: "x \<cdot> one = x"
    and l_inv: "inv x \<cdot> x = one"
    and r_inv: "x \<cdot> inv x = one"

lemma (in group) l_cancel: "(x \<cdot> y = x \<cdot> z) = (y = z)"
proof
  assume "x \<cdot> y = x \<cdot> z"
  then have "(inv x \<cdot> x) \<cdot> y = (inv x \<cdot> x) \<cdot> z" by (simp add: assoc)
  then show "y = z" by (simp add: l_one l_inv)
next
  assume "y = z"
  then show "x \<cdot> y = x \<cdot> z" by simp
qed

subsection {* Export *}

thm semi.assoc group.l_cancel

subsection {* Definitions *}

locale semi2 = semi +
  fixes rprod (infixl "\<odot>" 70)
  defines rprod_def: "rprod x y \<equiv> y \<cdot> x "

lemma (in semi2) r_assoc:
  "(x \<odot> y) \<odot> z = x \<odot> (y \<odot> z)"
  by (simp only: rprod_def assoc)

thm semi2.r_assoc

section {* Example 2 *}

locale group_hom = group sum zero minus + group +
  fixes hom
  assumes hom_mult: "hom (sum x y) = hom x \<cdot> hom y"

lemma (in group_hom) hom_one: "hom zero = one"
proof -
  have "hom zero \<cdot> one = hom zero \<cdot> hom zero"
    by (simp add: hom_mult [symmetric]
      sum_zero_minus.l_one prod_one_inv.r_one)
    -- {* Or add @{text l_one} to simpset right away. *}
  then show ?thesis by (simp add: l_cancel)
qed

section {* Example 3 *}

lemma int_semi:
  "semi (op +::[int, int]=>int)"
  by (auto intro!: semi.intro)

lemma int_group:
  "group (op +) (0::int) uminus"
  by (auto intro!: group.intro semi.intro group_axioms.intro)

text {* Manual interpretation possible with the OF attribute. *}

thm semi.assoc [OF int_semi]
thm group.l_cancel [OF int_group]

text {* Automatic interpretation *}

lemma bla: True
proof -
  from int_group interpret my: group ["op +" "0::int" "uminus"]
    by (auto intro: group.axioms)
  thm my.assoc my.l_cancel
oops

end
