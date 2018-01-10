theory Exe2p11
  imports Main
begin

datatype exp = Var | Const int | Add exp exp | Mult exp exp

fun eval :: "exp \<Rightarrow> int \<Rightarrow> int" where
"eval Var i = i" |
"eval (Const i) _ = i" |
"eval (Add e1 e2) i = (eval e1 i) + (eval e2 i)" |
"eval (Mult e1 e2) i = (eval e1 i) * (eval e2 i)"

fun evalp :: "int list \<Rightarrow> int \<Rightarrow> int" where
"evalp [] x = 0" |
"evalp (h#t) x = h + (evalp t x) * x"

fun trimp :: "int list \<Rightarrow> int list" where
"trimp [] = []" |
"trimp (h#t) = (if h = 0
                then (if length (trimp t) = 0
                      then []
                      else (h#trimp t))
                else (h#trimp t))" 

fun addp :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
"addp [] xs = xs" |
"addp xs [] = xs" |
"addp (h1#t1) (h2#t2) = (h1 + h2) # (addp t1 t2)"

fun multp :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
"multp [] _ = []" |
"multp (h#t) l = addp (map (op * h) l) (0 # multp t l)" 

fun coeffs :: "exp \<Rightarrow> int list" where
"coeffs Var = [0,1]" |
"coeffs (Const z) = [z]" |
"coeffs (Add e1 e2) = addp (coeffs e1) (coeffs e2)" |
"coeffs (Mult e1 e2) = multp (coeffs e1) (coeffs e2)"

lemma [simp]: "addp xs [] = xs"
  apply(induction xs)
   apply(auto)
  done

lemma [simp]: "evalp (addp l1 l2) x = evalp l1 x + evalp l2 x"
  apply(induction l1 rule: addp.induct)
    apply(auto simp add: algebra_simps)
  done

lemma [simp]: "evalp (multp l []) x = 0"
  apply(induction l)
   apply(auto)
  done

lemma [simp]: "evalp (multp l (h # t)) x = h * evalp l x + x * (evalp (multp l t) x)"
  apply(induction l)
   apply(auto simp add: algebra_simps)
  done

lemma [simp]: "evalp (multp l1 l2) x = evalp l1 x * evalp l2 x"
  apply(induction l1 rule: multp.induct)
   apply(auto simp add: algebra_simps)
  done

lemma "evalp (coeffs e) x = eval e x"
  apply(induction e arbitrary: x)
   apply(auto simp add: algebra_simps)
  done
