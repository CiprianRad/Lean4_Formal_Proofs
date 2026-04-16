import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Data.Int.Basic
import Mathlib.Tactic
/- EXERCISE 4

  Replace the first sorry with the smallest possible value and
  Proove that the values of the polynomial on {0,1,2} are in that range.

  Hint: use `fin_cases`
-/
example (n : ℕ) (h : n ∈ Finset.range 3) : n^4 - n + 3 ∈ Finset.range 18 := by
  fin_cases h -- We use fin_cases to split what we need to show into a finite amount of cases (3). And close all of themm with norm_num tactic
  . norm_num
  . norm_num
  . norm_num

example (n : ℕ) (h : n ∈ Finset.range 3) : n^4 - n + 3 ∈ Finset.range 18 := by
  fin_cases h <;> norm_num -- We use fin_cases to split what we need to show into a finite amount of cases (3). And close all of themm with norm_num tactic

def divisors (n : Nat) : List Nat :=
  (List.range (n + 1)).filter (fun d => d > 0 && n % d =0)

#eval divisors 969

/- EXERCISE 17
-/
example {a : ℤ} (ha : Odd a) : Odd (a ^ 2 + 2 * a - 4) := by
  dsimp [Odd] at * --Simplifying the definition of `Odd` in context and goal
  obtain ⟨k₁, h1⟩ := ha --We consume the existential quantifier, splitting it into 2 different hypothesis
  use 2*k₁^2 + 4*k₁ -1 -- We find the right replacement for `k` in the definition of `Odd` in goal.
  calc --We use a calc chain to prove the goal by rewriting and `ring` tactic
    a ^ 2 + 2 * a - 4 = (2 * k₁ + 1) ^ 2 + 2 * (2 * k₁ + 1) - 4 := by rw[h1]
    _ = 4 * k₁ ^ 2 + 4 * k₁ + 1 + 4 * k₁ + 2 - 4 := by ring
    _ = 4 * k₁ ^ 2 + 8 * k₁ - 1 := by ring
    _ = 2 * (2*k₁^2 + 4*k₁ -1) + 1 := by ring


/- EXERCISE 23
-/
example {a b : ℤ} (hab : a ∣ b) : a ∣ 2 * b ^ 3 - b ^ 2 + 3 * b := by
  obtain ⟨k₁, h2⟩ := hab --We consume the existential quantifier, obtaining 2 different hypothesis
  use 2 * a ^ 2 * k₁ ^ 3 - a * k₁ ^ 2 + 3 * k₁ --We find the right replacement for `k` in the the definition of divisibility
  calc --We use a calc chain to get to the correct form of the goal using `rw` and `ring`
    2 * b ^ 3 - b ^ 2 + 3 * b = 2 * (a * k₁) ^ 3 - (a * k₁) ^ 2 + 3 * (a * k₁) := by rw[h2]
    _ = a * (2 * a ^ 2 * k₁ ^ 3 - a * k₁ ^ 2 + 3 * k₁) := by ring


example {a b : ℤ} (hab : a ∣ b) : a ∣ 2 * b ^ 3 - b ^ 2 + 3 * b := by
  apply Exists.elim hab
  intro k₁ h2
  use 2 * a ^ 2 * k₁ ^ 3 - a * k₁ ^ 2 + 3 * k₁
  calc
    2 * b ^ 3 - b ^ 2 + 3 * b = 2 * (a * k₁) ^ 3 - (a * k₁) ^ 2 + 3 * (a * k₁) := by rw[h2]
    _ = a * (2 * a ^ 2 * k₁ ^ 3 - a * k₁ ^ 2 + 3 * k₁) := by ring



--EXTRA:

/- EXERCISE 9

  Replace the first sorry with the divisors of the indicated number.
  Prove that all elements in that set divide the indicated number.

  Hint: use `fin_cases`
-/
def s₉: Finset Nat := {1, 2, 4, 13, 26, 52 , 169, 338, 676}
example (n : ℕ) : n ∈ s₉ → n ∣ 676 := by
  intro hn
  fin_cases hn
  <;> decide


/- EXERCISE 18
-/
example {p : ℤ} (hp : Odd p) : Odd (p ^ 2 + 3 * p - 5) := by
  dsimp [Odd] at *
  obtain ⟨k, h1⟩ := hp
  use 2 * k ^ 2 + 5 * k - 1
  calc
    p ^ 2 + 3 * p - 5 = (2 * k + 1) ^ 2 + 3 * (2 * k + 1) - 5 := by rw[h1]
    _ = 2 * (2 * k ^ 2 + 5 * k - 1) + 1 := by ring


/- EXERCISE 19
-/
example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x * y) := by
  dsimp [Odd] at *
  obtain ⟨k, h1⟩ := hx
  obtain ⟨l, h2⟩ := hy
  use 2 * l * k + k + l
  calc
    x * y = (2 * k + 1) * (2 * l + 1) := by rw[h1, h2]
    _ = 2 * (2 * l * k + k + l) + 1 := by ring

/- EXERCISE 20
-/
example {n : ℤ} (hn : n + 3 = 7) : ¬ (Even n ∧ n ^ 2 = 10) := by
  push_neg
  intro h
  dsimp [Even] at *
  obtain ⟨k, h1⟩ := h
  by_contra h2
  have h2' : 10 = n ^ 2 := by rw[Eq.symm h2]
  have h3 : n = 4 :=
    calc
      n = (n + 3) - 3 := by norm_num
      _ = 7 - 3 := by rw[hn]
      _ = 4 := by norm_num
  have h4 : n ^ 2 = 16 :=
    calc
      n ^ 2 = 4 ^ 2 := by rw[h3]
      _ = 16 := by norm_num
  have h5: (10 : ℤ) = 16 :=
    calc
      10 = n ^ 2 := h2'
      _ = 16 := by rw[h4]
  contradiction



/- # Divisibility
  The following exercises are from
  https://hrmacbeth.github.io/math2001/03_Parity_and_Divisibility.html#exercises
-/

/- EXERCISE 21
-/
example {x y : ℤ} (h : x ∣ y) : x ∣ 3 * y - 4 * y ^ 2 := by
  obtain ⟨a, hy⟩ := h
  use 3 * a - 4 * x * a ^ 2
  calc
    3 * y - 4 * y ^ 2 = 3 * (x * a) - 4 * (x * a) ^ 2 := by rw[hy]
    _ = x * (3 * a - 4 * x * a ^ 2) := by ring

/- EXERCISE 22
-/
example {m n : ℤ} (h : m ∣ n) : m ∣ 2 * n ^ 3 + n := by
  obtain ⟨a, hn⟩ := h
  use 2 * m ^ 2 * a ^ 3 + a
  calc
    2 * n ^ 3 + n = 2 * (m * a) ^ 3 + (m * a) := by rw[hn]
    _ = m * (2 * m ^ 2 * a ^ 3 + a) := by ring

/- EXERCISE 23
-/
example {a b : ℤ} (hab : a ∣ b) : a ∣ 2 * b ^ 3 - b ^ 2 + 3 * b := by
  obtain ⟨k₁, h2⟩ := hab
  use 2 * a ^ 2 * k₁ ^ 3 - a * k₁ ^ 2 + 3 * k₁
  calc
    2 * b ^ 3 - b ^ 2 + 3 * b = 2 * (a * k₁) ^ 3 - (a * k₁) ^ 2 + 3 * (a * k₁) := by rw[h2]
    _ = a * (2 * a ^ 2 * k₁ ^ 3 - a * k₁ ^ 2 + 3 * k₁) := by ring

/- EXERCISE 24
-/
example {k l m : ℤ} (h1 : k ∣ l) (h2 : l ^ 3 ∣ m) : k ^ 3 ∣ m := by
  obtain ⟨a, hl1⟩ := h1
  obtain ⟨b, hl2⟩ := h2
  use a ^ 3 * b
  calc
    m = l ^ 3 * b := hl2
    _ = (k * a) ^ 3 * b := by rw[hl1]
    _ = k ^ 3 * (a ^ 3 * b) := by ring


/- EXERCISE 25
-/
example {p q r : ℤ} (hpq : p ^ 3 ∣ q) (hqr : q ^ 2 ∣ r) : p ^ 6 ∣ r := by
  obtain ⟨a, hq⟩ := hpq
  obtain ⟨b, hr⟩ := hqr
  use a ^ 2 * b
  calc
    r = q ^ 2 * b := hr
    _ = (p ^ 3 * a) ^ 2 * b := by rw[hq]
    _ = p ^ 6 * (a ^ 2 * b) := by ring



/-
  Bounded functions exercises
-/

def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

def FnHasUb (f : ℝ → ℝ) :=
  ∃ a, FnUb f a

def FnHasLb (f : ℝ → ℝ) :=
  ∃ a, FnLb f a

#check add_le_add_left
#check add_le_add_right

/- ECERCISE 31
-/
example{f g : ℝ → ℝ} (lbf : FnHasLb f) (lbg : FnHasLb g) : FnHasLb fun x ↦ f x + g x := by
  obtain ⟨a, h1⟩ := lbf
  obtain ⟨b, h2⟩ := lbg
  use a + b
  intro x
  dsimp
  have ha : a ≤ f x := h1 x
  have hb : b ≤ g x := h2 x
  calc
    a + b ≤ f x + b := add_le_add_right ha b
    _     ≤ f x + g x := add_le_add_left hb (f x)





/- EXERCISE 32
-/
example {f g : ℝ → ℝ} {c : ℝ} (ubf : FnHasUb f) (h : c ≥ 0) : FnHasUb fun x ↦ c * f x := by
  obtain ⟨a, h1⟩ := ubf
  use c * a
  intro x
  dsimp
  have := by exact mul_le_mul_of_nonneg_left (h1 x) h
  exact this

  --calc
    --c * f x ≤ c * a := by exact mul_le_mul_of_nonneg_left (h1 x) h





/-
  Absolute value exercises
-/

/- EXERCISE 34

  This is theorem `abs_lt` from Mathlib
  Prove it without invoking the Mathlib theorem
-/
example (x y : ℝ) : |x| < y ↔ -y < x ∧ x < y := by
  cases le_or_gt 0 x
  . case inl h =>
    rw[abs_of_nonneg h]
    constructor
    . case mp =>
      intro hx
      constructor
      . case left =>
        linarith
      . case right =>
        exact hx
    . case mpr =>
      intro hy
      obtain ⟨h1, h2⟩ := hy
      exact h2
  . case inr h =>
    rw[abs_of_neg h]
    constructor
    . case mp =>
      intro hx
      constructor
      . case left =>
        linarith
      . case right =>
        linarith
    . case mpr =>
      intro hy
      obtain ⟨h1, h2⟩ := hy
      linarith




#check abs_lt

example (x y : ℝ) : |x| < y ↔ -y < x ∧ x < y := by
  constructor
  . case mp =>
    intro hx
    apply abs_lt.mp hx
  . case mpr =>
    intro hx
    apply abs_lt.mpr hx


example (x y : ℝ) : |x| < y ↔ -y < x ∧ x < y := by exact abs_lt
