theory Exe4p2
  imports Main
begin

lemma "(\<exists> ys zs. xs = ys @ zs \<and> length ys = length zs)
      \<or>(\<exists> ys zs. xs = ys @ zs \<and> length ys = length zx + 1)"
proof 
  