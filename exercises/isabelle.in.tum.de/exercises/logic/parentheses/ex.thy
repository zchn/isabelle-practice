(*
    $Id: ex.thy,v 1.3 2012/01/04 13:40:21 webertj Exp $
    Author: Tobias Nipkow
*)

header {* Context-Free Grammars *}

(*<*) theory ex imports Main begin (*>*)

text {* This exercise is concerned with context-free grammars (CFGs).
Please read Section~7.4 in the tutorial which explains how to model
CFGs as inductive definitions.  Our particular example is about
defining valid sequences of parentheses. *}

subsection {* Two grammars *}

text {* The most natural definition of valid sequences of parentheses is this:
\[ S \quad\to\quad \varepsilon \quad\mid\quad '('~S~')' \quad\mid\quad S~S \]
where $\varepsilon$ is the empty word.

A second, somewhat unusual grammar is the following one:
\[ T \quad\to\quad \varepsilon \quad\mid\quad T~'('~T~')' \]

Model both grammars as inductive sets $S$ and $T$ and prove $S = T$. *}


subsection {* A recursive function *}

text {* Instead of a grammar, we can also define valid sequences of
parentheses via a test function:  traverse the word from left to right
while counting how many closing parentheses are still needed.  If the
counter is 0 at the end, the sequence is valid.

Define this recursive function and prove that a word is in $S$ iff it
is accepted by your function.  The $\Longrightarrow$ direction is easy,
the other direction more complicated. *}


(*<*) end (*>*)
