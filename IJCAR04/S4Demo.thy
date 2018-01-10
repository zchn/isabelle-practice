theory DemoComp = Main:

datatype binop = Plus | Minus | Mult

datatype 'v expr = Const nat
                 | Var 'v
                 | Binop binop "'v expr"  "'v expr"

consts semop :: "binop \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" ("\<lbrakk>_\<rbrakk>")
primrec 
  "\<lbrakk>Plus\<rbrakk> = (\<lambda>x y. x + y)"
  "\<lbrakk>Minus\<rbrakk> = (\<lambda>x y. x - y)"
  "\<lbrakk>Mult\<rbrakk> = (\<lambda>x y. x * y)"

consts value :: "'v expr \<Rightarrow> ('v \<Rightarrow> nat) \<Rightarrow> nat"
primrec 
  "value (Const v) E = v"
  "value (Var a) E = E a"   
  "value (Binop f e\<^isub>1 e\<^isub>2) E = \<lbrakk>f\<rbrakk> (value e\<^isub>1 E) (value e\<^isub>2 E)";

datatype 'v instr = Push nat
                  | Load 'v
                  | Apply binop

consts exec :: "'v instr list \<Rightarrow> ('v \<Rightarrow> nat) \<Rightarrow> nat list \<Rightarrow> nat list"
primrec
  "exec [] s vs = vs"
  "exec (i#is) s vs = (case i of
    Push v  \<Rightarrow> exec is s (v # vs)
  | Load a  \<Rightarrow> exec is s (s a # vs)
  | Apply f \<Rightarrow> let v\<^isub>1 = hd vs; v\<^isub>2 = hd (tl vs); ts = tl (tl vs) in 
               exec is s (\<lbrakk>f\<rbrakk> v\<^isub>1 v\<^isub>2 # ts))"

consts cmp :: "'v expr \<Rightarrow> 'v instr list"
primrec
  "cmp (Const v) = [Push v]"
  "cmp (Var a) = [Load a]"
  "cmp (Binop f e\<^isub>1 e\<^isub>2) = (cmp e\<^isub>2) @ (cmp e\<^isub>1) @ [Apply f]"


theorem "exec (cmp e) s [] = [value e s]"














oops
-- solution

lemma exec_append [simp]:
  "\<And>st. exec (is\<^isub>1@is\<^isub>2) s st = exec is\<^isub>2 s (exec is\<^isub>1 s st)"
proof (induct is\<^isub>1)
  fix st show "exec ([] @ is\<^isub>2) s st = exec is\<^isub>2 s (exec [] s st)" by simp
next
  fix st i "is" 
  assume IH: "\<And>st. exec (is@is\<^isub>2) s st = exec is\<^isub>2 s (exec is s st)" 
  show "exec ((i#is) @ is\<^isub>2) s st = exec is\<^isub>2 s (exec (i#is) s st)"
  proof (cases i)
    fix n assume "i = Push n" then show ?thesis by (simp add: IH)
  next
    fix v assume "i = Load v" then show ?thesis by (simp add: IH)
  next
    fix f assume "i = Apply f" then show ?thesis by (simp add: IH Let_def)
  qed
qed

lemma correct:
  "\<And>st. exec (cmp e) s st = value e s # st"
proof (induct e)
  fix st n
  show "exec (cmp (Const n)) s st = value (Const n) s # st" by simp
next
  fix st v 
  show "exec (cmp (Var v)) s st = value (Var v) s # st" by simp
next
  fix st f e\<^isub>1 e\<^isub>2 
  assume 
    "\<And>st. exec (cmp e\<^isub>1) s st = value e\<^isub>1 s # st" and
    "\<And>st. exec (cmp e\<^isub>2) s st = value e\<^isub>2 s # st" 
  then
  show "exec (cmp (Binop f e\<^isub>1 e\<^isub>2)) s st = value (Binop f e\<^isub>1 e\<^isub>2) s # st"
    by (simp add: Let_def)
qed

corollary "exec (cmp e) s [] = [value e s]" by (rule correct)

end
