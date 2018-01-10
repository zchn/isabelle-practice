theory Demo2 imports Main begin

subsection{* moreover/ultimately *}

(*
thm mono_def
*)

lemma assumes monof: "mono(f::int\<Rightarrow>int)"
          and monog: "mono(g::int\<Rightarrow>int)"
      shows "mono(\<lambda>i. f i + g i)"
proof --"rule monoI used automatically"
  fix i j :: int
  assume A: "i \<le> j"
  from A monof have "f i \<le> f j" by(simp add:mono_def)
  moreover
  from A monog have "g i \<le> g j" by(simp add:mono_def)
  ultimately show "f i + g i \<le> f j + g j" by arith
qed



subsection{* also/finally *}

declare ring_eq_simps [simp]

subsection{* Monotonicity reasoning *}
lemma "(a+b::int)\<twosuperior> \<le> 2*(a\<twosuperior> + b\<twosuperior>)"
proof -
       have "(a+b)\<twosuperior> \<le> (a+b)\<twosuperior> + (a-b)\<twosuperior>"  by simp
  also have "(a+b)\<twosuperior> \<le> a\<twosuperior> + b\<twosuperior> + 2*a*b"  by(simp add:numeral_2_eq_2)
  also have "(a-b)\<twosuperior> = a\<twosuperior> + b\<twosuperior> - 2*a*b"  by(simp add:numeral_2_eq_2)
  finally show ?thesis by simp
qed


end
