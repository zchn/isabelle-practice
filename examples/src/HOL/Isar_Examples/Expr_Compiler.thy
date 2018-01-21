(*  Title:      HOL/Isar_Examples/Expr_Compiler.thy
    Author:     Makarius

Correctness of a simple expression/stack-machine compiler.
*)

section \<open>Correctness of a simple expression compiler\<close>

theory Expr_Compiler
  imports Main
begin

text \<open>
  This is a (rather trivial) example of program verification. We model a
  compiler for translating expressions to stack machine instructions, and
  prove its correctness wrt.\ some evaluation semantics.
\<close>


subsection \<open>Binary operations\<close>

text \<open>
  Binary operations are just functions over some type of values. This is both
  for abstract syntax and semantics, i.e.\ we use a ``shallow embedding''
  here.
\<close>

type_synonym 'val binop = "'val \<Rightarrow> 'val \<Rightarrow> 'val"


subsection \<open>Expressions\<close>

text \<open>
  The language of expressions is defined as an inductive type, consisting of
  variables, constants, and binary operations on expressions.
\<close>

datatype (dead 'adr, dead 'val) expr =
    Variable 'adr
  | Constant 'val
  | Binop "'val binop" "('adr, 'val) expr" "('adr, 'val) expr"

text \<open>
  Evaluation (wrt.\ some environment of variable assignments) is defined by
  primitive recursion over the structure of expressions.
\<close>

primrec eval :: "('adr, 'val) expr \<Rightarrow> ('adr \<Rightarrow> 'val) \<Rightarrow> 'val"
  where
    "eval (Variable x) env = env x"
  | "eval (Constant c) env = c"
  | "eval (Binop f e1 e2) env = f (eval e1 env) (eval e2 env)"


subsection \<open>Machine\<close>

text \<open>
  Next we model a simple stack machine, with three instructions.
\<close>

datatype (dead 'adr, dead 'val) instr =
    Const 'val
  | Load 'adr
  | Apply "'val binop"

text \<open>
  Execution of a list of stack machine instructions is easily defined as
  follows.
\<close>

primrec exec :: "(('adr, 'val) instr) list \<Rightarrow> 'val list \<Rightarrow> ('adr \<Rightarrow> 'val) \<Rightarrow> 'val list"
  where
    "exec [] stack env = stack"
  | "exec (instr # instrs) stack env =
      (case instr of
        Const c \<Rightarrow> exec instrs (c # stack) env
      | Load x \<Rightarrow> exec instrs (env x # stack) env
      | Apply f \<Rightarrow> exec instrs (f (hd stack) (hd (tl stack)) # (tl (tl stack))) env)"

definition execute :: "(('adr, 'val) instr) list \<Rightarrow> ('adr \<Rightarrow> 'val) \<Rightarrow> 'val"
  where "execute instrs env = hd (exec instrs [] env)"

subsection \<open>Compiler\<close>

text \<open>
  We are ready to define the compilation function of expressions to lists of
  stack machine instructions.
\<close>

primrec compile :: "('adr, 'val) expr \<Rightarrow> (('adr, 'val) instr) list"
  where
    "compile (Variable x) = [Load x]"
  | "compile (Constant c) = [Const c]"
  | "compile (Binop f e1 e2) = compile e2 @ compile e1 @ [Apply f]"


text \<open>
  The main result of this development is the correctness theorem for
  \<open>compile\<close>. We first establish a lemma about \<open>exec\<close> and list append.
\<close>

lemma exec_append:
  "exec (xs @ ys) stack env =
    exec ys (exec xs stack env) env"
proof (induct xs arbitrary: stack ys)
  case Nil
  then show ?case by auto
next
  case (Cons a xs)
  then show ?case 
  proof (induct a)
    case (Const x)
    then show ?case by auto
  next
    case (Load x)
    then show ?case by auto
  next 
    case (Apply x)
    then show ?case by auto
  qed  
qed
  
  
theorem correctness: "execute (compile e) env = eval e env"
proof -
  have "\<And>st. exec (compile e) st env = eval e env # st"
  proof (induct e arbitrary: env)
    case (Variable x)
    then show ?case by simp
  next
    case (Constant x)
    then show ?case by simp
  next
    case (Binop x1a e1 e2)
    then show ?case by (simp add: exec_append)
  qed
  thus ?thesis by (simp add: execute_def)
qed

text \<open>
  \<^bigskip>
  In the proofs above, the \<open>simp\<close> method does quite a lot of work behind the
  scenes (mostly ``functional program execution''). Subsequently, the same
  reasoning is elaborated in detail --- at most one recursive function
  definition is used at a time. Thus we get a better idea of what is actually
  going on.
\<close>

lemma exec_append':
  "exec (xs @ ys) stack env = exec ys (exec xs stack env) env"
  oops
  
theorem correctness': "execute (compile e) env = eval e env"
  oops

end
