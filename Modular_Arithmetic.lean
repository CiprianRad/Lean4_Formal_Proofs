import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic


/- EXERCISE 4
-/
example (n : ℤ) : 3 * n ^ 2 + n - 2 ≡ 0 [ZMOD 2] := by
  mod_cases h : n % 2 --Since n is an integer, we split into cases in terms of the remainder when divided by 2 (even or odd)
  calc
    3 * n ^ 2 + n - 2 ≡ 3 * 0 ^ 2 + 0 - 2 [ZMOD 2] := by rel[h] --We rewrite n in the polynomial considering the operation on ℤ₂
    _ ≡ 0 [ZMOD 2] := by norm_num
  calc
    3 * n ^ 2 + n - 2 ≡ 3 * 1 ^ 2 + 1 - 2 [ZMOD 2] := by rel[h] --We rewrite n in the polynomial considering the operation on ℤ₂


/- EXERCISE 12
-/
example (n : ℕ) : 6 ^ n ≡ 1 [ZMOD 7] ∨ 6 ^ n ≡ 6 [ZMOD 7] := by
  induction' n with n hn
  . norm_num  --Base case: numerical equation - it can be closed by norm_num
  . rcases hn --Since in the induction hypothesis we have a disjunction, we split it by rcases
    . expose_names
      . right -- Constructing the right side of the disjunction in the goal
        calc
          6 ^ (n + 1) = (6 : ℤ) * 6 ^ n := by ring
          _ ≡ 6 * 1 [ZMOD 7] := by rel[h]
    . expose_names
      . left -- Constructing the left side of the disjunction in the goal.
        calc
          6 ^ (n + 1) = 6 * 6 ^ n := by ring
          _ ≡ 6 * 6 [ZMOD 7] := by rel[h]


#check Int.lcm_dvd
/- EXERCISE 30
-/
example {n : ℕ} (h1 : 8 ∣ n) (h2 : 15 ∣ n) : 120 ∣ n := by
  apply Nat.lcm_dvd h1 h2 --Since n ∈ ℕ , and lcm(8,15) = 120, then the goal fits the exact Mathlib lemma.

example {n : ℤ} (h1 : 8 ∣ n) (h2 : 15 ∣ n) : 120 ∣ n := by
  obtain ⟨k, hk⟩ := h1 --Since n ∈ ℤ, we cannot apply the lemma above, so we rewrite what it means that 8 ∣ n.
  obtain ⟨l, hl⟩ := h2 --Ibidem
  dsimp [(. ∣ .)]
  use 2 * l - k
  calc
    n = 1 * n := by ring
    _ = (2 * 8 - 15) * n := by norm_num
    _ = 2 * (8 * n) - 15 * n := by ring
    _ = 2 * (8 * (15 * l)) - 15 * (8 * k) := by nth_rw 1 [hl]; rw[hk]
    _ = 120 * (2 * l - k) := by ring
