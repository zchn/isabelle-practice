(*
    $Id: sol.thy,v 1.2 2004/11/23 15:14:35 webertj Exp $
*)

header {* A Riddle: Rich Grandfather *}

(*<*) theory sol imports Main begin (*>*)

text {*
  First prove the following formula, which is valid in classical predicate
  logic, informally with pen and paper.  Use case distinctions and/or proof by
  contradiction.

  {\it  If every poor man has a rich father,\\
   then there is a rich man who has a rich grandfather.}
*}

theorem
  "\<forall>x. \<not> rich x \<longrightarrow> rich (father x) \<Longrightarrow>
  \<exists>x. rich (father (father x)) \<and> rich x" (*<*) oops (*>*)

text {*
\begin{tabbing}
{\bf Proof} \\
(1)\ \= We first show: @{term "\<exists>x. rich x"}. \\
Proof by contradiction. \\
    \> {\bf Assume} \=  @{term "\<not> (\<exists>x. rich x)"}. \\
    \>               \> Then @{term "\<forall>x. \<not> rich x"}. \\
    \>               \> We consider an arbitrary @{term "y"} with
                          @{term "\<not> rich y"}. \\
    \>               \> Then @{term "rich (father y)"}. \\
(2) \> Now we show the theorem. \\
Proof by cases. \\
    \> {\bf Case 1:} \> @{term "rich (father (father x))"}. \\
    \>               \> We are done. \\ 
    \> {\bf Case 2:} \> @{term "\<not> rich (father (father x))"}. \\  
    \>               \> Then @{term "rich (father (father (father x)))"}. \\
    \>               \> Also @{term "rich (father x)"}, \\
    \>               \> because otherwise @{term "rich (father (father x))"}. \\
{\bf qed} \\
\end{tabbing}
*}

text {*
  Now prove the formula in Isabelle using a sequence of rule applications (i.e.\
  only using the methods @{term rule}, @{term erule} and @{term assumption}).
*}

theorem
  "\<forall>x. \<not> rich x \<longrightarrow> rich (father x) \<Longrightarrow>
  \<exists>x. rich (father (father x)) \<and> rich x"
apply (rule classical)
apply (rule exI)
apply (rule conjI)
  
  apply (rule classical)
  apply (rule allE) apply assumption
  apply (erule impE) apply assumption
  apply (erule notE) 
  apply (rule exI)
  apply (rule conjI) apply assumption
  apply (rule classical)
  apply (erule allE)
  apply (erule notE)
  apply (erule impE) apply assumption
  apply assumption

apply (rule classical)
apply (rule allE) apply assumption
apply (erule impE) apply assumption
apply (erule notE)
apply (rule exI)
apply (rule conjI) apply assumption
apply (rule classical)
apply (erule allE)
apply (erule notE)
apply (erule impE) apply assumption
apply assumption
done

text {*
  Here is a proof in Isar that resembles the informal reasoning above:
*}

theorem rich_grandfather: "\<forall>x. \<not> rich x \<longrightarrow> rich (father x) \<Longrightarrow> 
  \<exists>x. rich x \<and> rich (father (father x))"
proof -
  assume a: "\<forall>x. \<not> rich x \<longrightarrow> rich (father x)"
  txt {* (1) *} have "\<exists>x. rich x"
  proof (rule classical)
    fix y 
    assume "\<not> (\<exists>x. rich x)"
    then have "\<forall>x. \<not> rich x" by simp 
    then have "\<not> rich y" by simp
    with a have "rich (father y)" by simp
    then show ?thesis by rule 
  qed
  then obtain x where x: "rich x" by auto
  txt {* (2) *} show ?thesis
  proof cases
    assume "rich (father (father x))"
    with x show ?thesis by auto
  next
    assume b: "\<not> rich (father (father x))"
    with a have "rich (father (father (father x)))" by simp
    moreover have "rich (father x)" 
    proof (rule classical)
      assume "\<not> rich (father x)" 
      with a have "rich (father (father x))" by simp
      with b show ?thesis by contradiction 
    qed
    ultimately show ?thesis by auto
  qed
qed

(*<*) end (*>*)
