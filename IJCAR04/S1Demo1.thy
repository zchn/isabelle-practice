(* A simple comment *)

theory S1Demo1 imports Main begin

text {* This is also a comment but it generates nice \LaTeX-text! *}

text {*
 Note that free variables (eg x), bound variables (eg %n) and
 constants (eg Suc) are displayed differently.  *}

term "x"
term "Suc x"
term "Succ x"
term "Suc x = Succ y"
prop "Suc y = Suc y"

text{* To display types: menu Isabelle/Isar -> Settings -> Show Types *}

text {* Warning: 0 and + are overloaded: *}

prop "n + n = 0"
prop "(n::nat) + n = 0"
prop "n + n = Suc m"

text{* A bound variable: *}

prop "map (\<lambda>n. Suc n + 1) [0, 1] = [2, 3]"

(*
Try this:

term "Suc n = True"

Terms must be type correct!
*)

end
