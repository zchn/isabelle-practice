(*
    $Id: ex.thy,v 1.3 2012/08/13 15:59:05 webertj Exp $
    Author: Tobias Nipkow
*)

header {* The Towers of Hanoi *}

(*<*) theory ex imports Main begin (*>*)

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
*}

consts
  move :: "nat => peg => peg => move list"

text {*
such that @{term move}$~n~a~b$ returns a list of (legal) moves that transfer
$n$ disks from peg $a$ to peg $c$.
*}


text {*
Show that this requires $2^n - 1$ moves:
*}

theorem "length (move n a b) = 2^n - 1"
(*<*) oops (*>*)

text {*
Hint: You need to strengthen the theorem for the induction to go through.
Beware: subtraction on natural numbers behaves oddly: $n - m = 0$ if $n \le m$.
*}


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


(*<*) end (*>*)
