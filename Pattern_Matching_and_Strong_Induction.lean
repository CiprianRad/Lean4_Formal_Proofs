import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Cases --- for induction'

/- EXERCISE 4

  You may need `norm_cast` in `... := by rw [IH1,IH2]; norm_cast`
-/
def d : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => 9 * d (n + 1) - 20 * d n

example (n : ℕ) : d n = 5 ^ n - 4 ^ n := by
  induction' n  using  Nat.twoStepInduction with n IH1 IH2  --We use two step induction, since our sequence is defined recursively with a dependency on both `n+1` and `n`
  . rw[d] --The zero case can be closed with a simple rewrite and we are left with a numerical inequality.
    norm_num
  . rw [d]
    norm_num -- Ibidem for the zero case
  . calc
    d (n + 2) = 9 * d (n + 1) - 20 * d (n) := by rw[d] -- We make use of the definition of the integer valued sequence which is a recursive definition
    _ = 9 * (5 ^ (n + 1) - 4 ^ (n + 1)) - 20 * (5 ^ n - 4 ^ n) := by rw[IH1, IH2] --We replace the `n+1` and `n` terms with the induction hypotheses.
    _ = 5 ^ (n + 2) - 4 ^ (n + 2) := by ring -- We use `ring` to bring the equality to the one in the goal.


/- EXERCISE 12
-/
def B : ℕ → ℤ
  | 0 => 0
  | 1 => 0
  | 2 => 4
  | n + 3 => 6 * B (n+2) - 11 * B (n+1) + 6 * B n


lemma lemma_B (n : ℕ) : B n = 2 + (-4)*2 ^ n + (2)* 3 ^ n := by
  match n with  -- Since the sequence above is defined recursive with thrice a dependency, we use a generalization of induction with pattern_matching.
  | 0 => -- For the 0-3 cases we know we remain only with a numerical equality to prove and we close them all with norm_num
    rw [B]
    norm_num
  | 1 =>
    rw[B]
    norm_num
  | 2 =>
    rw [B]
    norm_num
  | (n + 3) =>
    have IH1 := lemma_B n --Since we did not specifically use the `induction'` tactic, we need to explicitly extract the induction hypothesis.
    have IH2 := lemma_B (n + 1) --Ibidem
    have IH3 :=  lemma_B (n + 2)  --Ibidem
    calc
      B (n + 3) = 6 * B (n + 2) - 11 * B (n + 1) + 6 * B n := by rw[B] --We make use of the recursive defenition of the B integer sequence above.
      _ = 6 * ( 2 + (-4)*2 ^ (n+2) + (2)* 3 ^ (n+2)) - 11 * ( 2 + (-4)*2 ^ (n+1) + (2)* 3 ^ (n+1)) + 6 * ( 2 + (-4)*2 ^ n + (2)* 3 ^ n) := by rw[IH1, IH2, IH3]  --We make use of the induction hypothesis in the inequality and replace all we can.
      _ =  2 + (-4)*2 ^ (n + 3) + (2)* 3 ^ (n + 3) := by ring --We bring the equality to the form of the one in the goal using `ring` tactic.

/- EXERCISE 21

   perhaps `nlinarith` will help at some step
-/

example (n : ℕ) : 2*(5 ^ n) ≥ n ^ 2  + n := by
  induction' n using Nat.twoStepInduction with n _ IH  --We need a two step induction, but only the second hypothesis with `n+1` is of interest, the other can be discarded, so we just leave a placeholder for it.
  . norm_num --The first case is a numerical inequality.
  . norm_num --Ibidem
  .
    have h := --We first make use of the induction hypothesis with `n+1` to find an upper bound for `2 * 5 ^ (n + 2)`
      calc
        2 * 5 ^ (n + 2) = 5 * (2 * 5 ^ (n + 1)) := by ring
        _ ≥ 5 * ((n + 1) ^ 2 + (n + 1)) := by rel[IH]
        _ = 5 * n ^ 2 + 15 * n + 10 := by ring --We find an upper bound and now we want to show that the upper bound in the goal is an upper bound for the upper bound.
    have h' :=
      calc
        5 * n ^ 2 + 15 * n + 10 ≥ 5 * n ^ 2 + 15 * n + 10  - (4 * n ^ 2 + 10 * n + 4) := by exact Nat.sub_le (5 * n ^ 2 + 15 * n + 10) (4 * n ^ 2 + 10 * n + 4) --We manipulate the expression to get to the upper bound in the goal
        _ = n ^ 2 + 5 * n + 6 := by omega --Since we have used a `Nat` theorem, our expression is now in (ℕ,+). We therefore apply the `omega` tactic that deals with Natural and Integer linear expressions.
        _ = (n + 2) ^ 2 + (n + 2) := by ring --We bring the upper bound in the form of the one in the goal
    exact Nat.le_trans h' h --We use the transitivity of ` ≤ ` over `ℕ`.
