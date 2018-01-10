theory Demo1 imports Main begin

section{* How to simplify *}

text{* No assumption: *}
lemma "ys @ [] = []"
apply simp
oops

text{* Simple assumption: *}
lemma "xs = [] \<Longrightarrow> xs @ ys = ys @ xs @ ys"
apply simp
oops

text{* Simplification in assumption: *}
lemma "\<lbrakk> xs @ zs = ys @ xs; [] @ xs = [] @ [] \<rbrakk> \<Longrightarrow> ys = zs"
apply simp
done

text{* 
  This assumption would lead to nontermination.
  (Note that ALL binds stronger than ==>)
*}
lemma "\<forall>x. f x = g x \<and> g x = f x \<Longrightarrow> f [] = f [] @ []"
(* Would diverge:
apply(simp)
*)
apply(simp (no_asm))
done

text{* Using additional rules: *}
lemma "(a+b)*(a-b) = a*a - b*(b::int)"
apply(simp add: ring_distrib right_diff_distrib)
done

text{* Giving a lemma the simp-attribute: *}
declare ring_distrib [simp]


subsection{* Tracing: *}

lemma "rev [x] = []"
apply simp
oops

subsection{* Auto *}

text{* Method ``auto'' can be modified almost like ``simp'': instead of
``add'' use ``simp add'': *}

lemma "(\<exists>u::nat. x=y+u) \<longrightarrow> a*(b+c)+y \<le> x + a*b+a*c"
apply(auto simp add: add_mult_distrib2)
done

end
