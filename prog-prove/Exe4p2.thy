theory Exe4p2
  imports Main
begin

lemma "\<not>surj(f :: 'a \<Rightarrow> 'a set)"
proof
  assume "surj f"
  hence "\<exists>a.{x. x\<notin>f x} = f a" by (auto simp: surj_def)
  thus "False" by blast
qed

lemma "(\<exists>ys zs. xs = ys @ zs \<and> length ys = length zs)
    \<or> (\<exists>ys zs. xs = ys @ zs \<and> length ys = length zs + 1)" (is "(\<exists>ys zs. ?P ys zs ?xs) \<or> (\<exists>ys zs. ?Q ys zs ?xs)")
proof cases
  assume "length xs mod 2 = 0"
  obtain ys where "ys = take (length xs div 2) xs" by auto
  obtain zs where "zs = drop (length xs div 2) xs" by auto
  show ?thesis by blast
next
  assume "length xs mod 2 \<noteq> 0"
  obtain ys where "ys = take (length xs div 2) xs" by auto
  obtain zs where "zs = drop (length xs div 2) xs" by auto
  show ?thesis by blast
qed

end