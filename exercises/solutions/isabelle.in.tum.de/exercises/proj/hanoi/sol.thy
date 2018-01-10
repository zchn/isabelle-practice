(*
    $Id: sol.thy,v 1.5 2012/08/13 15:59:05 webertj Exp $
    Author: Gerwin Klein
*)

header {* The Towers of Hanoi *}

(*<*) theory sol imports Main begin (*>*)

text {*
We are given 3 pegs $A$, $B$ and $C$, and $n$ disks with a hole, such that no
two disks have the same diameter.  Initially all $n$ disks rest on peg $A$,
ordered according to their size, with the largest one at the bottom.  The aim
is to transfer all $n$ disks from $A$ to $C$ by a sequence of single-disk moves
such that we never place a larger disk on top of a smaller one.  Peg $B$ may be
used for intermediate storage.

\begin{center}
\includegraphics[width=0.8\textwidth]{Hanoi}
\end{center}

\medskip The pegs and moves can be modelled as follows:
*}

datatype peg = A | B | C

type_synonym move = "peg * peg"

text {*
Define a primitive recursive function

  @{text "move :: nat => peg => peg => move list"}

such that @{term move}$~n~a~b$ returns a list of (legal) moves that transfer
$n$ disks from peg $a$ to peg $c$.
*}

primrec other :: "peg \<Rightarrow> peg \<Rightarrow> peg" where
  "other A x = (if x = B then C else B)"
| "other B x = (if x = A then C else A)"
| "other C x = (if x = A then B else A)"

primrec move :: "nat \<Rightarrow> peg \<Rightarrow> peg \<Rightarrow> move list" where
  "move 0       src dst = []"
| "move (Suc n) src dst = (move n src (other src dst)) @ [(src,dst)] @ (move n (other src dst) dst)"


text {*
Show that this requires $2^n - 1$ moves:
*}

theorem "length (move n a b) = 2^n - 1"
(*<*) oops (*>*)

text {*
Hint: You need to strengthen the theorem for the induction to go through.
Beware: subtraction on natural numbers behaves oddly: $n - m = 0$ if $n \le m$.
*}

lemma "\<forall>x y. length (move n x y) = 2^n - 1"
  apply (induct n)
    apply simp
  apply auto
done


subsection {* Correctness *}

text {*
In the last section we introduced the towers of Hanoi and defined a function
@{term move} to generate the moves to solve the puzzle.  Now it is time to show
that @{term move} is correct.  This means that
\begin{itemize}
\item when executing the list of moves, the result is indeed the intended one,
      i.e.\ all disks are moved from one peg to another, and
\item all of the moves are legal, i.e.\ never is a larger disk placed on top of
      a smaller one.
\end{itemize}

Hint: This is a non-trivial undertaking.  The complexity of your proofs will
depend crucially on your choice of model, and you may have to revise your model
as you proceed with the proof.
*}

type_synonym
  config = "peg \<Rightarrow> nat list"

primrec lt :: "nat \<Rightarrow> nat list \<Rightarrow> bool" where
  "lt n [] = True"
| "lt n (x#xs) = (n < x \<and> lt n xs)"

primrec ordered :: "nat list \<Rightarrow> bool" where
  "ordered [] = True"
 | "ordered (x#xs) = (lt x xs \<and> ordered xs)"

definition hanoi :: "config \<Rightarrow> bool" where
  "hanoi cfg \<equiv> \<forall>s. ordered (cfg s)"

definition step :: "config \<Rightarrow> move \<Rightarrow> config option" where
  "step c x \<equiv> let (src,dst) = x in 
    if c src = [] then None
    else let src' = tl (c src); 
             m = hd (c src); 
             dst' = m # (c dst);
             c' = (c (src:= src')) (dst:= dst') 
         in if hanoi c' then Some c' else None"

primrec exec :: "config \<Rightarrow> move list \<Rightarrow> config option" where
  "exec c [] = Some c"
| "exec c (x#xs) = (let cfg' = step c x in if cfg' = None then None else exec (the cfg') xs)"

primrec tower :: "nat \<Rightarrow> nat list" where
  "tower 0 = []"
| "tower (Suc n) = tower n @ [Suc n]"

lemma [simp]:
  "other x y \<noteq> x \<and> other x y \<noteq> y"
  by (cases x, auto)

lemma "move 1 A C = [(A,C)]"
  by simp

lemma "move 2 A C = [(A, B), (A, C), (B, C)]"
  by (simp add: numeral_2_eq_2)

lemma "move 3 A C = [(A, C), (A, B), (C, B), (A, C), (B, A), (B, C), (A, C)]"
  by (simp add: numeral_3_eq_3)

lemma [simp]:
  "\<forall>cfg. exec cfg (a@b) = (let cfg' = exec cfg a in if cfg' = None then None else exec (the cfg') b)"
  by (induct a, auto simp add: Let_def)
 
lemma neq_Nil_snoC:
  "\<forall>n. length xs = Suc n \<longrightarrow> (\<exists>x' xs'. xs = xs' @ [x'])"
  apply (induct xs)
  apply simp
  apply clarsimp
  apply (case_tac xs)
   apply simp
  apply clarsimp
  done

lemma otherF [simp]: "x = other x y \<Longrightarrow> False"
  apply (cases x, auto split: split_if_asm)
  done

lemma [simp]: "x\<noteq>y \<Longrightarrow> other x (other x y) = y"
  apply (cases x)
  apply (cases y, auto)+
  done

lemma [simp]: "x\<noteq>y \<Longrightarrow> other (other x y) y = x"
  apply (cases x)
  apply (cases y, auto)+
  done

primrec gt :: "nat \<Rightarrow> nat list \<Rightarrow> bool" where
  "gt n [] = True"
| "gt n (x#xs) = (x < n \<and>  gt n xs)"

lemma [simp]:
  "lt n (a@b) = (lt n a \<and> lt n b)"
  apply (induct a)
  apply auto
  done

lemma [simp]:
  "gt n (a@b) = (gt n a \<and> gt n b)"
  apply (induct a)
  apply auto
done

lemma lt_mono [rule_format, simp]:
  "a < b \<longrightarrow> lt b xs \<longrightarrow> lt a xs"
  apply (induct xs)
  apply auto
done

lemma [simp]:
  "ordered (a@n#b) = (ordered a \<and> lt n b \<and> gt n a \<and> ordered b)"
  apply (induct a)
   apply simp
  apply auto
done  
  
lemma gt_iff:
  "gt n xs = (\<forall>x \<in> set xs. x < n)"
  by (induct xs, auto)
  
lemma [simp]:
  "xs \<noteq> [] \<longrightarrow> last xs \<in> set xs"
  by (induct xs, auto)

lemma [simp]:
  "\<lbrakk>cfg src = ts' @ t' # xs; hanoi cfg; ts' \<noteq> []\<rbrakk> \<Longrightarrow> last ts' < t'"
  apply (unfold hanoi_def)
  apply (erule_tac x = src in allE)
  apply (clarsimp simp add: gt_iff)
done

lemma neq_other:
  "\<lbrakk> s \<noteq> src; s \<noteq> dst; src\<noteq>dst \<rbrakk> \<Longrightarrow> s = other src dst"
  apply (cases src, auto)
  apply (cases s, auto)
  apply (cases s, auto)
  apply (cases dst, auto)
  apply (cases s, auto)
  apply (cases s, auto)
  apply (cases dst, auto)
  apply (cases s, auto)
  apply (cases s, auto)  
  apply (cases dst, auto)
  done

lemma ordered_appendI [rule_format]:
  "ordered a \<longrightarrow> lt t b \<longrightarrow> gt t a \<longrightarrow> ordered b \<longrightarrow> ordered (a@b)"
  by (induct a, auto)

lemma [simp]:
  "\<forall>cfg. exec cfg xs = Some cfg' \<longrightarrow> hanoi cfg \<longrightarrow> hanoi cfg'"
  apply (induct xs)
   apply simp
  apply (auto simp add: step_def Let_def split: split_if_asm)
done

lemma hanoi_lemma:
  "\<forall>cfg src dst t xs ys zs. 
       cfg src = t @ xs \<longrightarrow> cfg dst = ys \<longrightarrow> cfg (other src dst) = zs \<longrightarrow> 
       length t = n \<longrightarrow>
       hanoi cfg \<longrightarrow> 
       lt (last t) ys \<longrightarrow> lt (last t) zs \<longrightarrow>
       src \<noteq> dst \<longrightarrow>
  (\<exists>cfg'. exec cfg (move n src dst) = Some cfg' \<and> cfg' src = xs \<and> cfg' dst = t @ ys \<and> cfg' (other src dst) = zs)"
apply (induct n) 
 apply simp
apply clarsimp
apply (case_tac "n=0")
 apply (simp add: Let_def)
 apply (case_tac t)
  apply simp
 apply simp
 apply (rule conjI)
  apply (clarsimp simp add: step_def Let_def hanoi_def)
  apply (erule_tac x = src in allE)
  apply simp
 apply (clarsimp simp add: step_def Let_def)
apply clarsimp
apply (subgoal_tac "\<exists>t' ts'. t = ts' @ [t']")
 prefer 2 
 apply (simp add: neq_Nil_snoC)
apply clarsimp
apply (frule spec, erule allE, erule_tac x = "other src dst" in allE, erule allE, erule allE, erule impE, assumption)
apply (erule impE, rule refl)
apply (erule impE, assumption)
apply simp
apply (subgoal_tac "last ts' < t'")
 apply (erule impE)
  apply (erule lt_mono, assumption)
 apply (erule impE)
  apply (erule lt_mono, assumption)
 apply (erule impE)
  apply rule
  apply (erule otherF)
 prefer 2
 apply simp 
apply clarsimp
apply (clarsimp simp add: Let_def)
apply (rule conjI)
 apply (clarsimp simp add: step_def Let_def hanoi_def)
 apply (rule conjI)
  apply (erule_tac x=src in allE)
  apply clarsimp
 apply clarsimp
 apply (drule neq_other, assumption, assumption)
 apply simp
 apply (frule_tac x="other src dst" in spec)
 apply (drule_tac x="src" in spec)
 apply clarsimp
 apply (rule ordered_appendI, assumption+)
apply (clarsimp simp add: step_def Let_def)
apply (erule_tac x="cfg'(src := xs, dst := t' # cfg dst)" in allE)
apply (erule_tac x="other src dst" in allE)
apply (erule_tac x="dst" in allE)
apply (erule allE)+ 
apply (erule impE)
 apply simp
apply (erule impE, rule refl)
apply (erule impE)
 apply simp
apply (erule impE)
 apply simp 
 apply (rule lt_mono)
 apply (subgoal_tac "last ts' < t'")
  prefer 2 
  apply simp
 apply assumption+
apply (erule impE)
 apply (subgoal_tac "last ts' < t'")
  prefer 2 
  apply simp
 apply (unfold hanoi_def)
 apply (erule_tac x = src in allE)
 apply (erule lt_mono)
 apply simp
apply clarsimp
done

lemma [simp]: "length (tower n) = n"
  by (induct n, auto)

lemma "lt 0 (tower n)"
  by (induct n, auto)

lemma gt_mono [rule_format, simp]: "x < y \<longrightarrow> gt x xs \<longrightarrow> gt y xs"
  apply (induct xs)
  apply auto
done

lemma [simp]: "gt (Suc n) (tower n)"
  apply (induct n)
  apply auto
  apply (rule gt_mono)
  defer
  apply assumption
  apply simp
done

lemma [simp]: "ordered (tower n)"
  apply (induct n)
  apply auto
done

lemma hanoi_start:
  "\<lbrakk> cfg A = tower n; cfg B = []; cfg C = [] \<rbrakk> \<Longrightarrow>
  hanoi cfg"
  apply (unfold hanoi_def)
  apply (rule allI)
  apply (case_tac s)
  apply auto
done

theorem hanoi:
  "\<lbrakk>cfg A = tower n; 
    cfg B = []; 
    cfg C = []\<rbrakk> \<Longrightarrow> 
  \<exists>cfg'. exec cfg (move n A C) = Some cfg' \<and> 
    cfg' A = [] \<and>
    cfg' B = [] \<and>
    cfg' C = tower n"
  apply (frule hanoi_start, assumption+)
  apply (insert hanoi_lemma [of n])
  apply (erule_tac x=cfg in allE)
  apply (erule_tac x=A in allE)
  apply (erule_tac x=C in allE)
  apply (erule_tac x="tower n" in allE)
  apply (erule allE)+
  apply (erule impE)
   apply simp
  apply (erule impE, assumption)+
  apply (erule impE, simp)
  apply clarsimp
done


(*<*) end (*>*)
