(*
    $Id: sol.thy,v 1.3 2011/06/28 18:11:39 webertj Exp $
    Author: Gerwin Klein
*)

header {* Compilation with Side Effects *}

(*<*) theory sol imports Main begin (*>*)

text {*
This exercise deals with the compiler example in Section~3.3 of the
Isabelle/HOL tutorial.  The simple side effect free expressions are extended
with side effects.

\begin{enumerate}
\item Read Sections~3.3 and~8.2 of the Isabelle/HOL tutorial.  Study the
      section about @{text fun_upd} in theory @{text Fun} of HOL: @{text
      "fun_upd f x y"}, written @{text "f(x:=y)"}, is @{text f} updated at
      @{text x} with new value @{text y}.

\item Extend data type @{text "('a, 'v) expr"} with a new alternative @{text
      "Assign x e"} that shall represent an assignment @{text "x = e"} of the
      value of the expression @{text e} to the variable @{text x}.  The value
      of an assignment shall be the value of @{text e}.

\item Modify the evaluation function @{text value} such that it can deal with
      assignments.  Note that since the evaluation of an expression may now
      change the environment, it no longer suffices to return only the value
      from the evaluation of an expression.

      Define a function @{text "se_free :: expr \<Rightarrow> bool"} that
      identifies side effect free expressions.  Show that @{text "se_free e"}
      implies that evaluation of @{text e} does not change the environment.

\item Extend data type @{text "('a, 'v) instr"} with a new instruction @{text
      "Store x"} that stores the topmost element on the stack in
      address/variable @{text x}, without removing it from the stack.  Update
      the machine semantics @{text exec} accordingly.  You will face the same
      problem as in the extension of @{text value}.

\item Modify the compiler @{text comp} and its correctness proof to accommodate
      the above changes.
\end{enumerate}
*}

type_synonym 'v binop = "'v \<Rightarrow> 'v \<Rightarrow> 'v"

datatype ('a, 'v) exp 
  = Const 'v 
  | Var 'a 
  | Binop "'v binop" "('a, 'v) exp" "('a, 'v) exp"
  | Assign 'a "('a, 'v) exp"

primrec val :: "('a, 'v) exp => ('a => 'v) => 'v * ('a => 'v)" where
  "val (Const c)       env = (c, env)"
| "val (Var x)         env = (env x, env)"
| "val (Binop f e1 e2) env =
     (let (x, env1) = val e1 env;
          (y, env2) = val e2 env1
      in (f x y, env2))"
| "val (Assign a e)    env =
     (let (x, env') = val e env
      in (x, env' (a := x)))"

primrec se_free :: "('a, 'v) exp \<Rightarrow> bool" where
  "se_free (Const c)       = True"
| "se_free (Var x)         = True"
| "se_free (Binop f e1 e2) = (se_free e1 \<and> se_free e2)"
| "se_free (Assign x e)    = False"

lemma "se_free e \<longrightarrow> snd (val e env) = env"
  apply (induct_tac e)
     apply simp
    apply simp
   apply (simp add: Let_def split_def)
  apply simp
  done

datatype ('a, 'v) instr
  = CLoad 'v
  | VLoad 'a
  | Store 'a
  | Apply "'v binop"

primrec exec :: "('a, 'v) instr list \<Rightarrow> ('a \<Rightarrow> 'v) \<Rightarrow> 'v list \<Rightarrow> 'v list \<times> ('a \<Rightarrow> 'v)" where
  "exec [] hp vs = (vs, hp)"
| "exec (i#is) hp vs = (case i of
    CLoad v \<Rightarrow> exec is hp (v#vs)
  | VLoad a \<Rightarrow> exec is hp (hp a#vs)
  | Store a \<Rightarrow> exec is (hp (a:= hd vs)) vs
  | Apply f \<Rightarrow> exec is hp (f (hd (tl vs)) (hd vs)#(tl (tl vs))))"

lemma 
  "exec [CLoad (3::nat), 
         VLoad x, 
         CLoad 4,
         Apply (op *), 
         Apply (op +)] 
        (\<lambda>x. 0) [] = ([3], \<lambda>x. 0)"
  by simp

primrec comp :: "('a, 'v) exp \<Rightarrow> ('a, 'v) instr list" where
  "comp (Const c) = [CLoad c]"
| "comp (Var x) = [VLoad x]"
| "comp (Assign x e) = (comp e) @ [Store x]"
| "comp (Binop f e1 e2) = (comp e1) @ (comp e2) @ [Apply f]"

lemma [simp]:
  "\<forall>hp vs. exec (xs@ys) hp vs = (let (vs', hp') = exec xs hp vs in exec ys hp' vs')"
  apply (induct_tac xs)
  apply (simp add: Let_def)
  apply (simp add: Let_def split: instr.split)
  done

theorem [simp]:
  "\<forall>vs hp. exec (comp e) hp vs = ([fst (val e hp)] @ vs, snd (val e hp))"
  apply (induct_tac e)
     apply simp
    apply simp
   apply (simp add: Let_def split_def)
  apply (simp add: Let_def split_def)
  apply (simp add: fun_upd_def)  
  done  

corollary "exec (comp e) s [] = ([fst (val e s)], snd (val e s))"
  by simp


(*<*) end (*>*)
