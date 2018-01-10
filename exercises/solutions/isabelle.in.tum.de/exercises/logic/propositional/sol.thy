(*
    $Id: sol.thy,v 1.2 2004/11/23 15:14:35 webertj Exp $
*)

header {* Propositional Logic *}

(*<*) theory sol imports Main begin (*>*)

text {* In this exercise, we will prove some lemmas of propositional
logic with the aid of a calculus of natural deduction.

For the proofs, you may only use

\begin{itemize}
\item the following lemmas: \\
@{text "notI:"}~@{thm notI[of A,no_vars]},\\
@{text "notE:"}~@{thm notE[of A B,no_vars]},\\
@{text "conjI:"}~@{thm conjI[of A B,no_vars]},\\ 
@{text "conjE:"}~@{thm conjE[of A B C,no_vars]},\\
@{text "disjI1:"}~@{thm disjI1[of A B,no_vars]},\\
@{text "disjI2:"}~@{thm disjI2[of A B,no_vars]},\\
@{text "disjE:"}~@{thm disjE[of A B C,no_vars]},\\
@{text "impI:"}~@{thm impI[of A B,no_vars]},\\
@{text "impE:"}~@{thm impE[of A B C,no_vars]},\\
@{text "mp:"}~@{thm mp[of A B,no_vars]}\\
@{text "iffI:"}~@{thm iffI[of A B,no_vars]}, \\
@{text "iffE:"}~@{thm iffE[of A B C,no_vars]}\\
@{text "classical:"}~@{thm classical[of A,no_vars]}

\item the proof methods @{term rule}, @{term erule} and @{term assumption}.
\end{itemize}

Prove:
*}

lemma I: "A \<longrightarrow> A"
  apply (rule impI)
  apply assumption
done

lemma "A \<and> B \<longrightarrow> B \<and> A"
  apply (rule impI)
  apply (erule conjE)
  apply (rule conjI)
  apply assumption
  apply assumption
done

lemma "(A \<and> B) \<longrightarrow> (A \<or> B)"
  apply (rule impI)
  apply (erule conjE)
  apply (rule disjI1)
  apply assumption
done

lemma "((A \<or> B) \<or> C) \<longrightarrow> A \<or> (B \<or> C)"
  apply (rule impI)
  apply (erule disjE)
  apply (erule disjE)
  apply (rule disjI1)
  apply assumption
  apply (rule disjI2)
  apply (rule disjI1)
  apply assumption
  apply (rule disjI2)
  apply (rule disjI2)
  apply assumption
done

lemma K: "A \<longrightarrow> B \<longrightarrow> A"
  apply (rule impI)+
  apply assumption
done

lemma "(A \<or> A) = (A \<and> A)"
  apply (rule iffI)

  apply (erule disjE)
  apply (rule conjI)
  apply assumption+
  apply (rule conjI)
  apply assumption+

  apply (erule conjE)
  apply (rule disjI1)
  apply assumption
done

lemma S: "(A \<longrightarrow> B \<longrightarrow> C) \<longrightarrow> (A \<longrightarrow> B) \<longrightarrow> A \<longrightarrow> C"
  apply (rule impI)+
  apply (erule impE)
  apply assumption
  apply (erule impE)
  apply assumption
  apply (erule impE)
  apply assumption+
done

lemma "(A \<longrightarrow> B) \<longrightarrow> (B \<longrightarrow> C) \<longrightarrow> A \<longrightarrow> C"
  apply (rule impI)+
  apply (erule impE)
  apply assumption
  apply (erule impE)
  apply assumption+
done

lemma "\<not> \<not> A \<longrightarrow> A"
  apply (rule impI)
  apply (rule classical)
  apply (erule notE)
  apply assumption
done

lemma "A \<longrightarrow> \<not> \<not> A"
  apply (rule impI)
  apply (rule notI)
  apply (erule notE)
  apply assumption
done

lemma "(\<not> A \<longrightarrow> B) \<longrightarrow> (\<not> B \<longrightarrow> A)"
  apply (rule impI)+
  apply (rule classical)
  apply (erule impE)
  apply assumption
  apply (erule notE)
  apply assumption
done

lemma "((A \<longrightarrow> B) \<longrightarrow> A) \<longrightarrow> A"
  apply (rule impI)+
  apply (rule classical)
  apply (erule impE)
  apply (rule impI)
  apply (erule notE, assumption)+
done

lemma "A \<or> \<not> A"
  apply (rule classical)
  apply (rule disjI2)
  apply (rule notI)
  apply (erule notE)
  apply (rule disjI1)
  apply assumption
done

lemma "(\<not> (A \<and> B)) = (\<not> A \<or> \<not> B)"
  apply (rule iffI)

  apply (rule classical)
  apply (erule notE)
  apply (rule conjI)
  apply (rule classical)
  apply (erule notE)
  apply (rule disjI1)
  apply assumption
  apply (rule classical)
  apply (erule notE)
  apply (rule disjI2)
  apply assumption

  apply (rule notI)
  apply (erule conjE)
  apply (erule disjE)
  apply (erule notE, assumption)+
done

(*<*) end (*>*)
