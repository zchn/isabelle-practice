theory Exercises2 imports Main begin

subsection "primitive recursion and induction"

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

text {* 
  define a function that converts a tree into 
  a list in post order by primitive recursion 
*}

consts 
  postorder :: "'a tree \<Rightarrow> 'a list"



text {* 
  define another function that does the same, 
  but with tail recursion (recursive call at 
  top level only) 
*} 

consts
  postorder_it :: "['a tree, 'a list] \<Rightarrow> 'a list"



lemma "postorder_it t [] = postorder t"
  oops


subsection "inductively defined sets"

consts Ev :: "nat set"
inductive Ev
intros
ZeroI: "0 \<in> Ev"
Add2I: "n \<in> Ev \<Longrightarrow> Suc(Suc n) \<in> Ev"

lemma "\<lbrakk> n \<in> Ev; m \<in> Ev \<rbrakk> \<Longrightarrow> m+n \<in> Ev"
oops


text {* use method arith to solve linear arithmetic problems *}

lemma "n \<in> Ev \<Longrightarrow> \<exists>k. n = 2*k"
oops


lemma "n = 2*k \<longrightarrow> n \<in> Ev" 
oops


text {* Solve in Isar: *}

lemma "A \<and> B \<longrightarrow> B \<and> A"
oops

lemma "A \<and> (B \<or> C) \<longrightarrow> (A \<and> B) \<or> (A \<and> C)"
oops  


end