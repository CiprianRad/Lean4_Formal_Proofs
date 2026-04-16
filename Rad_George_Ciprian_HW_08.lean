import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Group
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Cases --- for induction'

#check Nat.zero_le
lemma extra_square_N {a b x : ℕ} : a * x^2 + b ≥ b := by
  apply le_add_of_nonneg_left
  apply Nat.zero_le

/- EXERCISE 8

  Hint: if you need to show that some square is nonnegative
  you may use the `extra_square_N` lemma above.
  !! It may be that you don't need the above lemma at all. !!
-/



#check Nat.sub_le

example (n : ℕ) : 2*(5 ^ n) ≥ n ^ 2  + 2*n + 1:= by
  induction' n with n ih --We use induction to prove the above statement. Using induction' allows us not to write the name of the base step and induciton step explicitly
  . norm_num -- The base case is a numerical inequality. It can be close with norm_num
  . calc
      2 * (5 ^ (n + 1)) = 2 * (5 ^ n) * 5 := by ring  -- We manipulate the expression to make it look like the induciton hypothesis
      _ ≥ (n ^ 2 + 2 * n + 1) * 5 := by rel[ih] --We use the induction hypothesis for the inequaulity
      _ = 5 * (n ^ 2) + 10 * n + 5 := by ring  --We manipulate the expression to allow the usage of Nat.sub_le lemma from Mathlib
      _ ≥ 5 * (n ^ 2) + 10 * n + (5 - 1) := by exact Nat.sub_le (5 * n ^ 2 + 10 * n + 5) 1 --We use the lemma to get rid of some extra 1 in the inequality in the goal
      _ = 5 * (n ^ 2) + 4 + 10 * n := by ring --ibidem 2 steps before
      _ ≥ 5 * (n ^ 2) + 4 + 10 * n - 6 * n := by exact Nat.sub_le (5 * n ^ 2 + 4 + 10 * n) (6 * n) --Ibidem 2 steps before
      _ = 4 * n + 4 + 5 * (n ^ 2) := by omega --Since we have use Nat.sub_le lemma that works only on Naturals, we deal with Natural number subtraction which cannot be manipulate  by the `ring` or `group` tactic since (ℕ,+) is not a group.
      --We can however use the omega tactic which resolve integer and natural linear arithmetic expressions. Otherwise one would have to do a cast in the inequality and see it in a ring like ℤ or any other numerical ring, and the manipulate it and in the end cast it down to ℕ again for the goal.
      _ ≥ 4 * n + 4 + 5 * (n ^ 2) - 4 * (n ^ 2) := by exact Nat.sub_le (4 * n + 4 + 5 * n ^ 2) (4 * (n ^ 2))
      _ = n ^ 2 + 4 * n + 4 := by omega  --Likewise 2 steps before
      _ = (n + 1) ^ 2 + 2 *(n + 1) + 1 := by ring --Rewriting the epxression to match the goal


/- EXERCISE 15

  Here you will do induction from a certain point `N` onward.
  Hint: You may extend `induction'` with `Nat.le_induction`.
-/
example : ∃ N : ℕ, ∀ n : ℕ, n ≥ N → 3^n ≥ 3*n^2 + 3*n + 1 := by
  use 4 --By calculation it yields that N = 4
  intro n hn --We introduce the universal quantifier and the left hand side of the implication in context
  induction' n, hn using Nat.le_induction with n hn ih --We use induction with a lower bound. We specifiy the induction principle using Nat.le_induction.
  . norm_num --The base case, when n = 4, is a numerical inequality. It can be closed using norm_num
  .
    have h : (6 * n ^ 2 ≥ 4) := by --We introduce a helper inequality to reduce the extra n^2 terms in the inequality and add the natural number 4 to match the goal
      calc -- We use a calc chain and regular tactic to deduce the inequality in the hypothesis
        6 * n ^ 2 = (6 * n) * n := by ring
        _ ≥ (6 * n) * 4 := by rel[hn]
        _ = 24 * n := by ring
        _ ≥ 24 * 4 := by rel[hn]
        _ = 96 := by norm_num
        _ ≥ 4 := by norm_num
    have h' : (9 * n ^ 2 ≥ 3 * n ^ 2 + 4) := by --The completion of the hypothesis above. One could just make one hypothesis with a longer calc chain, however I took it step by step.
      calc
        9 * n ^ 2 = 3 * (n ^ 2) + 6 * (n ^ 2) := by ring
        _ ≥ 3 * n ^ 2 + 4 := by rel[h]
    calc  --A final calc chain for proving the Natural number inequality, using the induction hypothesis and the hypothesis above.
      3 ^ (n + 1) = 3 * (3 ^ n) := by ring
      _ ≥ 3 * (3 * (n ^2) + 3 * n + 1) := by rel[ih]
      _ = 9 * n ^ 2 + 9 * n + 3 := by ring
      _ ≥ (3 * n ^ 2 + 4) +9 * n + 3 := by rel[h']
      _ = 3 * n ^ 2 + 9 * n + 7 := by ring
      _ = 3 * (n + 1) ^ 2 + 3 * (n + 1) + 1 := by ring


/- Simple induction on the inductive type `MyNat`

  exercises form
  Mathematics in Lean
  5.2. Induction and Recursion
-/
inductive MyNat where
  | zero : MyNat
  | succ : MyNat → MyNat

namespace MyNat

def add : MyNat → MyNat → MyNat
  | x, zero => x
  | x, succ y => succ (add x y)

def mul : MyNat → MyNat → MyNat
  | _, zero => zero
  | x, succ y => add (mul x y) x

theorem zero_add (n : MyNat) : add zero n = n := by
  induction' n with n ih
  · rfl
  . rw [add, ih]

theorem add_zero (n : MyNat) : add n zero = n := by
  induction' n with n ih
  . rfl
  . rw[add]

theorem succ_add (m n : MyNat) : add (succ m) n = succ (add m n) := by
  induction' n with n ih
  · rfl
  . rw [add, ih]
    rfl

theorem add_comm (m n : MyNat) : add m n = add n m := by
  induction' n with n ih
  · rw [zero_add]
    rfl
  . rw [add, succ_add, ih]


theorem mul_one (n : MyNat) : mul (succ zero) n = n := by
  induction' n with n ih
  . rw[mul];
  . rw[mul , ih, add, add_zero]

theorem succ_eq_succ (m n: MyNat) : succ n = succ m ↔ n = m := by
  constructor
  . intro h
    cases h
    rfl
  . intro h
    cases h
    rfl


/- EXERCISE 21
-/
theorem add_assoc (m n k : MyNat) : add (add m n) k = add m (add n k) := by
  induction' n with n ih
  . rw[add, zero_add]
  . rw[succ_add, add, add_comm, add, add, succ_eq_succ, add_comm, ih]

/- EXERCISE 22
-/
theorem mul_add (m n k : MyNat) : mul m (add n k) = add (mul m n) (mul m k) := by
  induction' n with n ih
  . rw[zero_add, mul, zero_add]
  . rw[mul, succ_add, mul, ih, add_assoc, add_comm (mul  m k) m, add_assoc]

/- EXERCISE 23
-/
theorem zero_mul (n : MyNat) : mul zero n = zero := by
  induction' n with n ih
  . rw[mul]
  . rw[mul, ih]
    rfl

theorem mul_zero (n: MyNat) : mul n zero = zero := by
  induction' n with n ih
  . rw[mul]
  . rw[mul]

/- EXERCISE 24
-/
theorem succ_mul (m n : MyNat) : mul (succ m) n = add (mul m n) n := by
  induction' n with n ih --We use induction to prove the thoerem.
  . rw[mul, mul] --In the base case we rewrite what it means to multiply by zero in both the lfs and rhs.
    rfl --It can be close with rfl since zero add zero is zero.
  . rw[mul, ih, mul, add, add, succ_eq_succ, add_assoc, add_comm n m, add_assoc] --We do multiple rewrite using some of the theorems above as well, as well as the definitions for mul and add on MyNat. Of course using the induction hypothesis and the rewrites we get to the same expression on both sides and nothing else need be done



/- EXERCISE 25
-/
theorem mul_comm (m n : MyNat) : mul m n = mul n m := by
  induction' n with n ih
  . rw[mul_zero, zero_mul]
  . rw[succ_mul, mul, ih]

end MyNat
