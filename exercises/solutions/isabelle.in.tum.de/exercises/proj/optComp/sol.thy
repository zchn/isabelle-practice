(*
    $Id: sol.thy,v 1.4 2011/06/28 18:11:39 webertj Exp $
    Author: Farhad Mehta, Tobias Nipkow
*)

header {* Optimising Compilation for a Register Machine *}

(*<*) theory sol imports Main begin (*>*)

text {*\subsection*{The Source Language: Expressions}*}

text {*
The arithmetic expressions we will work with consist of variables, constants, and an arbitrary binary operator @{text "oper"}.
*}

consts
  oper :: "nat \<Rightarrow> nat \<Rightarrow> nat"

lemma operI:"\<lbrakk>a = c ; b = d\<rbrakk> \<Longrightarrow> oper a b = oper c d"
by simp

type_synonym var = string

datatype exp = 
    Const nat 
  | Var var
  | Op exp exp

text {*
The state in which an expression is evaluated is modelled by an {\em environment} function that maps variables to constants.
*}

type_synonym env = "var \<Rightarrow> nat"

text {*
The function @{text "value"} evaluates an expression in a given environment.
*}

primrec "value" :: "exp \<Rightarrow> env \<Rightarrow> nat" where
  "value (Const n) e = n"
| "value (Var v) e = (e v)"
| "value (Op e1 e2) e = (oper (value e1 e) (value e2 e))"

text {*\subsection*{The Register Machine}*}

text {*
Register indices and storage cells:
*}

type_synonym regIndex = nat

datatype cell = 
    Acc
  | Reg regIndex

text {*The instruction set:*}
datatype instr = 
    LI nat 
  | LOAD regIndex
  | STORE regIndex
  | OPER regIndex

type_synonym state = "cell \<Rightarrow> nat"

text {*Result of executing a single machine instruction:*}
primrec execi :: "state \<Rightarrow> instr \<Rightarrow> state" where
  "execi s (LI n) = (s (Acc := n))"
| "execi s (LOAD r) = (s (Acc := s(Reg r)))"
| "execi s (STORE r) = (s ((Reg r) := (s Acc)))"
| "execi s (OPER r) = (s (Acc := (oper (s (Reg r)) (s Acc))))"


text {*Result of serially executing a sequence of machine instructions:*}
definition exec :: "state \<Rightarrow> instr list \<Rightarrow> state" where
  "exec s instrs == foldl execi s instrs"

text {*Some lemmas about @{text "exec"}:*}

lemma exec_app:"exec s (p1 @ p2) = exec (exec s p1) p2"
by (clarsimp simp:exec_def)

lemma exec_null:"exec s [] = s"
by (clarsimp simp:exec_def)

lemma exec_cons:"exec s (i#is) = exec (execi s i) is"
by (clarsimp simp:exec_def)

lemma exec_sing:"exec s [i] = execi s i"
by (clarsimp simp:exec_def)

section{*Compilation*}

text {*A {\em mapping} function maps variables to positions in the register file.*}

type_synonym map = "var \<Rightarrow> regIndex"

text {*
The function @{text "cmp"} recursively translates an expression into a sequence of instructions that computes it. At the end of execution, the result is stored in the accumulator. In addition to a {\em mapping} function, @{text "cmp"} takes the next free register index as input.
*}

primrec cmp :: "exp \<Rightarrow> map \<Rightarrow> regIndex \<Rightarrow> instr list" where
  "cmp (Const n) m r = [LI n]"
| "cmp (Var v) m r = [(LOAD (m v))]"
| "cmp (Op e1 e2) m r = (cmp e1 m r)@[STORE r]@
                           (cmp e2 m (Suc r))@[OPER r]"


text {*The correctness lemma for @{text "cmp"}:*}

theorem corr_and_no_se:
  "\<And> st r. 
        \<lbrakk>\<forall>v. m v < r; \<forall>v. (env v) = (st (Reg (m v))) \<rbrakk> \<Longrightarrow>
        ((exec st (cmp e m r)) Acc = value e env) \<and>
        (\<forall>x. (x < r) \<longrightarrow> (((exec st (cmp e m r)) (Reg x)) = st (Reg x)))"
  (is "\<And> st r. \<lbrakk>?vars_below_r st r ;?var_vals st r \<rbrakk> \<Longrightarrow> 
                                   ?corr st e r \<and> ?no_side_eff st e r")

txt {*
Note:
\begin{itemize}
  \item We need some way of giving @{text "cmp"} the start index @{text "r"} of the free region in the register file. Initially, @{text "r"} should be above all variable mappings. The first assumption ensures this.
  \item All variable mappings should agree with the {\em environment} used in @{text "value"}. The second assumption ensures this.
  \item The first part of the conclusion expresses the correctness of @{text "cmp"}. 
  \item The second part of the conclusion expresses the fact that compilation does not use already allocated registers (i.e.\ those below @{text "r"}). This is needed for the inductive proof to go through.
\end{itemize}
*}

proof (induct e)
  case Const show ?case by (clarsimp simp:exec_def)
next
  case Var assume "?var_vals st r" then show ?case by (clarsimp simp:exec_def)
next
  case (Op e1 e2)
  assume hyp1:"\<And> st r. \<lbrakk>?vars_below_r st r ;?var_vals st r \<rbrakk> \<Longrightarrow> 
                         ?corr st e1 r \<and> ?no_side_eff st e1 r"
    and hyp2:"\<And> st r. \<lbrakk>?vars_below_r st r ;?var_vals st r \<rbrakk> \<Longrightarrow> 
                         ?corr st e2 r \<and> ?no_side_eff st e2 r"
    and vars_below_r:"?vars_below_r st r" and var_vals:"?var_vals st r"

  -- {* Four lemmas useful for simplification of main subgoal *}

  have rw1:"\<And>st x. \<lbrakk> x < (Suc r); ?var_vals st r \<rbrakk> \<Longrightarrow> 
                     exec st (cmp e2 m (Suc r)) (Reg x) = st (Reg x)"
  proof -
    fix st x
    assume a:"x < Suc r" and b:"?var_vals st r"
    from vars_below_r have "?vars_below_r st (Suc r)" 
      apply clarify 
      by (erule_tac x=v in allE, simp) 
    with a b hyp2[of "(Suc r)" "st"]  show "?thesis st x" by clarsimp
  qed

  have rw2:"\<And>st.?var_vals st r \<Longrightarrow> 
            exec st (cmp e2 m (Suc r)) Acc = value e2 env"
  proof -
    fix st
    assume a:"?var_vals st r"
    from vars_below_r have b: "?vars_below_r st (Suc r)"
      apply clarify 
      by (erule_tac x=v in allE, simp) 
    from b a show "?thesis st" 
      by (rule hyp2[THEN conjunct1,of "(Suc r)" "st"])
  qed  
 
  have rw3:"\<And>st x. \<lbrakk> x < r ; ?var_vals st r \<rbrakk> \<Longrightarrow> 
            exec st (cmp e1 m r) (Reg x) = st (Reg x)"
  proof -
    fix st x
    assume a:"x < r" and b:"?var_vals st r" 
    with vars_below_r hyp1[of "r" "st"]  show "?thesis st x" by clarsimp
  qed

  from vars_below_r var_vals 
  have val_e1:"exec st (cmp e1 m r) Acc = value e1 env"
    by (rule hyp1[THEN conjunct1,of "r" "st"]) 

  -- {* Two lemmas that express @{text "?var_vals"} also holds for the two states *}
  -- {* encountered in the proof of the main subgoal *}

  from vars_below_r var_vals 
  have vB1:"?var_vals ((exec st (cmp e1 m r)) 
            (Reg r := exec st (cmp e1 m r) Acc)) r"
    by (auto simp:rw3)

  from vars_below_r var_vals 
  have vB2:"?var_vals ((exec st (cmp e1 m r))(Reg r := value e1 env)) r"
    by (auto simp:rw3)

  show ?case
  proof
    show "?corr st (Op e1 e2) r"
      apply (simp add:exec_app exec_cons exec_null)
      apply (rule operI)
       apply (simp add:rw1 vB1 val_e1)
       apply (simp add:rw1 val_e1)
      apply (simp add:rw2 vB2)
      done
  next
    show "?no_side_eff st (Op e1 e2) r"
      apply clarify
      apply (simp add:exec_app exec_cons exec_null)
      apply (simp add:rw1 vB1)
      apply (simp add:rw3 var_vals)
      done
  qed
qed

section{*Compiler Optimisation: Common Subexpressions *}

text {*
The optimised compiler @{text "optCmp"}, should evaluate every commonly occurring subexpression only once.

General idea:
\begin{itemize}
  \item Generate a list of all sub-expressions occurring in a given expression. A given sub-expression in this list can only be 'one step' dependent on sub-expressions occurring earlier in the list. For example a possible list of sub-expressions for @{text "(a op b) op (a op b)"} is @{text "[a,b,a op b,a,b,a op b,(a op b) op (a op b)]"}.
  \item Note that the resulting sub-expression list specifies an order of evaluation for the given expression. The list in the above example is an evaluation sequence @{text "cmp"} would use. Since it contains duplicates, it is not what we want.
  \item Remove all duplicates from this list, in such a way, so as not to break the sub-expression list property (i.e.\ in case of a duplicate, remove the later occurance). For our example, this would result in @{text "[a,b,a op b,(a op b) op (a op b)]"}. 
  \item Evaluate all expressions in this list in the order that they occur. Store previous results somewhere in the register file and use them to evaluate later sub-expressions.
\end{itemize}
*}


text{* The previous {\em mapping} function is extended to include all expressions, not just variables.*}

type_synonym expMap = "exp \<Rightarrow> regIndex"

text{*
Instead of a single expression, the new compilation function takes as input a list of expressions. It is assumed that this list satisfies the sub-expression property discussed above.

At each step, it will compute the value of an expression, store it in the register file, and update the {\em mapping} function to reflect this.
*}

primrec optCmp :: "exp list \<Rightarrow> expMap \<Rightarrow> regIndex \<Rightarrow> instr list" where
  "optCmp [] m r = []"
| "optCmp (x#xs) m r = (case x of
    (Const n) \<Rightarrow> 
      [LI n]@[STORE r]@                      (optCmp xs (m(x := r)) (Suc r)) |
    (Var v) \<Rightarrow> 
      [(LOAD (m (Var v)))]@[STORE r]@        (optCmp xs (m(x := r)) (Suc r)) |
    (Op e1 e2) \<Rightarrow> 
      [LOAD (m e2)]@[OPER (m e1)]@[STORE r]@ (optCmp xs (m(x := r)) (Suc r))
  )"


text{*
The function @{text "alloc"} returns the register allocation done by @{text "optCmp"}: *}
primrec alloc :: "expMap \<Rightarrow> exp list \<Rightarrow> regIndex \<Rightarrow> expMap" where
  "alloc m [] r = m"
| "alloc m (e#es) r = alloc (m(e := r)) es (Suc r)"


text{*
Some lemmas about @{text "alloc"} and @{text "optCmp"}:*}

lemma allocApp:"\<And> m r. alloc m (as @ bs) r = 
                alloc (alloc m as r) bs (r + length as)"
by (induct as, auto)

lemma allocNotIn:"\<And>m r. e \<notin> set es \<Longrightarrow> alloc m es r e = m e"
by (induct es, auto)

text{*Sequential search in a list:*}
primrec search :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
  "search a [] = 0"
| "search a (x#xs) = (if (x=a) then 0 else Suc (search a xs))"

lemma searchLessLength:"\<And> a. a:set xs \<Longrightarrow> search a xs < length xs"
by (induct xs, auto)

lemma allocIn:"\<And>m r. \<lbrakk>distinct es; e \<in> set es\<rbrakk> \<Longrightarrow> 
                 (alloc m es r e) = r + search e es"
apply (induct es)
 apply (auto)
apply (frule_tac m="(m(e := r))" and r="(Suc r)" in allocNotIn)
apply simp
done

lemma optCmpApp:"\<And> i m r. i = length as \<Longrightarrow> 
  optCmp (as@bs) m r = (optCmp as m r) @ (optCmp bs (alloc m as r) (r+i))" 
apply (induct as)
 apply clarsimp
apply (case_tac a, auto)
done

text{*
The function  @{text "supExp"} expresses the converse of the sub-expression property discussed earlier:*}
primrec supExp :: "exp list \<Rightarrow> bool" where
  "supExp [] = True"
| "supExp (e#es) = (case e of 
                    (Const n) \<Rightarrow> supExp es |
                    (Var v) \<Rightarrow> supExp es  |
                    (Op e1 e2) \<Rightarrow> (supExp es) \<and> (e1 : set es) \<and> (e2 : set es) 
  )"


text{*
A definition of @{text "subExp"} using  @{text "supExp"} (a direct definition is harder!):*}
definition subExp :: "exp list \<Rightarrow> bool" where
  "subExp es == supExp (rev es)"

text{*
The correctness theorem for @{text "optCmp"}:*}
theorem opt_corr_and_no_se:
  "\<And> st r. 
        \<lbrakk>\<forall>e. (m e) < r; \<forall>v. (env v) = (st (Reg (m (Var v)))); 
                                      subExp es; distinct es \<rbrakk> \<Longrightarrow>
        (\<forall>e\<in>set es. (exec st (optCmp es m r)) (Reg ((alloc m es r) e)) 
        = value e env) \<and>
        (\<forall>x. (x < r) \<longrightarrow> (((exec st (optCmp es m r)) (Reg x)) = st (Reg x)))"
txt {*
Note:
\begin{itemize}
  \item As input, we have an arbitrary expression list that satisfies the sub-expression property.
  \item The assumption that this list is unique is not strictly required, but makes the proof easier.
  \item The rest of theorem bears resemblance to that of @{text "cmp"}.
\end{itemize}
*}
apply (induct es rule:rev_induct)
 apply (clarsimp simp: exec_cons exec_null)
apply (simp only:optCmpApp exec_app subExp_def)
apply (case_tac x)

  --"Const case"
  apply clarsimp
  apply rule
   apply (simp add:allocApp)
   apply (simp add:exec_cons exec_null)
  apply rule
   apply clarsimp
   apply (simp add:allocApp)
   apply rule
    apply (simp add:exec_cons exec_null)
   apply (simp add:exec_cons exec_null)
   apply clarsimp
   apply (frule_tac m="m" and e="e" and r="r" in allocIn)
    apply assumption
   apply (frule searchLessLength)
   apply simp
  apply clarsimp
  apply (simp add:exec_cons exec_null)

  --"Var case"
 apply clarsimp
 apply rule
  apply (simp add:allocApp)
  apply (simp add:exec_cons exec_null)
  apply (frule_tac m="m" and r="r" in allocNotIn)
  apply clarsimp
 apply (simp add:allocApp)
 apply rule
  apply clarsimp
  apply rule
   apply (clarsimp simp add:exec_cons exec_null)
  apply (clarsimp simp add:exec_cons exec_null)
  apply (frule_tac m="m" and e="e" and r="r" in allocIn)
   apply assumption
  apply (frule searchLessLength)
  apply simp
 apply clarsimp
 apply (simp add:exec_cons exec_null)

--"Op case"
apply clarsimp
apply rule
 apply (simp add:allocApp)
 apply (simp add:exec_cons exec_null)
apply (simp add:allocApp)
apply rule
 apply clarsimp
 apply rule
 apply (clarsimp simp add:exec_cons exec_null)
 apply (clarsimp simp add:exec_cons exec_null)
 apply (frule_tac m="m" and e="e" and r="r" in allocIn)
  apply assumption
 apply (frule_tac a="e" in searchLessLength)
 apply simp
apply clarsimp
apply (simp add:exec_cons exec_null)
done

text{*
Till now we have proven that @{text "optCmp"} is correct for an expression list that satisfies some properties. Now we show that one such list can be generated from any given expression.
*}

text{*
Pre-order traversal of an expression:
*}

primrec preOrd :: "exp \<Rightarrow> exp list" where
  "preOrd (Const n) = [Const n]"
| "preOrd (Var v) = [Var v]"
| "preOrd (Op e1 e2) = (Op e1 e2)#(preOrd e1 @ preOrd e2)"


lemma self_in_preOrd:"e \<in> set (preOrd e)" 
by(case_tac e, auto)

text{*
The function @{text "optExp"} generates a distinct sub-expression list from a given expression:
*}
definition optExp ::"exp \<Rightarrow> exp list" where
  "optExp e == rev (remdups (preOrd e))"

lemma distinct_rev:"distinct (rev xs) = distinct xs"
by (induct xs, auto)

lemma supExp_app:"\<And> bs. \<lbrakk> supExp as ; supExp bs \<rbrakk> \<Longrightarrow> supExp (as @ bs)"
apply (induct as)
 apply clarsimp
apply (case_tac a)
  apply auto
done

lemma supExp_remdups:"\<And> bs. supExp as \<Longrightarrow> supExp (remdups as)"
apply (induct as)
 apply clarsimp
apply (case_tac a)
  apply auto
done

lemma supExp_preOrd:"supExp (preOrd e)"
apply (induct e)
 apply (auto dest:supExp_app simp:self_in_preOrd )
done

text{*
Proof that a list generated by @{text "optExp"} is distinct and satisfies the sub-expression property:
*}

lemma optExpDistinct:"distinct(optExp e)"
by (simp add:optExp_def)

lemma optExpSupExp:"subExp (optExp e)"
apply (induct e)
 apply (auto simp:optExp_def self_in_preOrd subExp_def
        intro:supExp_remdups supExp_preOrd supExp_app)
done


text{*
Do @{text "optCmp"} @{text "optExp"} and generate code that evaluate all common sub-expressions only once?

Yes. Since @{text "optExp"} returns all commonly occurring sub-expressions only once, and @{text "optCmp"} evaluates these only once, all common sub-expressions are evaluated only once.
*}

text{*
But, for those of little faith:
*}

lemma opt:"\<And>m r. length (filter (\<lambda>e. \<exists>x y. e = (Op x y)) es) = 
                length (filter (\<lambda>i. \<exists>x. i = (OPER x)) (optCmp es m r))"
apply (induct es)
 apply clarsimp
apply (case_tac a)
  apply auto
done


end
 
