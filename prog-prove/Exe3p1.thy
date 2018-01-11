theory Exe3p1
  imports Main
begin

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun set :: "'a tree \<Rightarrow> 'a set" where
"set Tip = {}" |
"set (Node l n r) = {n} \<union> set l \<union> set r"

fun ord :: "int tree \<Rightarrow> bool" where
"ord Tip = True" |
"ord (Node l n r) = (\<not>(\<exists>x. x \<in> set l \<and> x > n) \<and> \<not>(\<exists>x. x \<in> set r \<and> x < n))"

fun ins :: "int \<Rightarrow> int tree \<Rightarrow> int tree" where
"ins x Tip = Node Tip x Tip" |
"ins x (Node l n r) = (
  if x = n then (Node l n r)
           else (if x < n then (Node (ins x l) n r)
                          else (Node l n (ins x r))))"

lemma ins_correctness_1 [simp]: "set (ins x t) = {x} \<union> set t"
  apply(induction t)
   apply(auto)
  done

lemma ins_correctness_2: "ord t \<Longrightarrow> ord (ins i t)"
  apply(induction t)
   apply(auto)
  done

thm conjI

thm conjI[of "a=b" "False"]

thm conjI[OF refl[of "a"] refl[of "b"]]
