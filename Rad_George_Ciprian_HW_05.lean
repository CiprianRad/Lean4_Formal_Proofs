import Mathlib.Data.Real.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith



/- EXERCISE 1
-/
example : ¬ (∃ n : ℕ, 26 * n = 3) := by
  push_neg
  intro n hn
  have h₁ := lt_trichotomy n 1
  rcases h₁ with (hl | hm | hr)
  . have h1 : n = 0 := by linarith
    rw[h1] at hn
    contradiction
  . rw[hm] at hn
    contradiction
  . have h3 : n ≥ 2 := by linarith
    have h4 :=
      calc
        3 = 26 * n := by rw[hn]
        26 * n ≥ 26 * 2 := by rel[h3]
        _ = 52 := by norm_num
    contradiction


/- EXERCISE 2
-/
#check ne_of_gt

example : ¬ (∃ n : ℕ, 47 * n = 2) := by
  push_neg --We push the logical operator not as far away into the proposition in the goal
  intro n hn --We introduce the variable and equality in the context
  have h₁ := lt_trichotomy n 1 --We introduce an extra hypothesis with the trichotomy property of the natural numbers
  rcases h₁ with (hl | hm | hr) --We split the disjunction in the hypothesis into 3 cases with `rcases`
  . have h1 : n = 0 := by linarith --We obtain the first value for n in the case n<1 and n natural number, thus 1
    rw[h1] at hn --Rewriting the value of n in the equality
    contradiction -- (0 : ℕ) = 2 is a trivial contradiction
  . rw[hm] at hn -- We rewrite the value of n=1 in the equality
    contradiction --(47 : ℕ) = 2 a trivial contradiction
  . have h3 : n ≥ 2 := by linarith -- We obtain this inequality from the third case where n>1 and n is a natural number
    have h4 :=
      calc
        2 = 47 * n := by rw[hn]
        47 * n ≥ 47 * 2 := by rel[h3]
        _ = 94 := by norm_num --We conclude that 2 ≥ 94 which is a trivial contradiction
    contradiction








/- EXERCISE 3
-/
example : ¬ (∃ n : ℕ, 19 * n = 3) := by
  push_neg
  intro n hn
  have h₁ := lt_trichotomy n 1
  rcases h₁ with (hl | hm | hr)
  . have h1 : n = 0 := by linarith
    rw[h1] at hn
    contradiction
  . rw[hm] at hn
    contradiction
  . have h3 : n ≥ 2 := by linarith
    have h4 :=
      calc
        3 = 19 * n := by rw[hn]
        19 * n ≥ 19 * 2 := by rel[h3]
        _ = 38 := by norm_num
    contradiction

/- EXERCISE 4
-/
example : ¬ (∃ n : ℕ, 17 * n = 2) := by
  push_neg
  intro n hn
  have h₁ := lt_trichotomy n 1
  rcases h₁ with (hl | hm | hr)
  . have h1 : n = 0 := by linarith
    rw[h1] at hn
    contradiction
  . rw[hm] at hn
    contradiction
  . have h3 : n ≥ 2 := by linarith
    have h4 :=
      calc
        2 = 17 * n := by rw[hn]
        17 * n ≥ 17 * 2 := by rel[h3]
        _ = 34 := by norm_num
    contradiction

/- EXERCISE 5
-/
example : ¬ (∃ n : ℕ, 22 * n = 1) := by
  push_neg
  intro n hn
  have h₁ := lt_trichotomy n 1
  rcases h₁ with (hl | hm | hr)
  . have h1 : n = 0 := by linarith
    rw[h1] at hn
    contradiction
  . rw[hm] at hn
    contradiction
  . have h3 : n ≥ 2 := by linarith
    have h4 :=
      calc
        1 = 22 * n := by rw[hn]
        22 * n ≥ 22 * 2 := by rel[h3]
        _ = 44 := by norm_num
    contradiction

/- EXERCISE 11
-/
example (p q r : Prop): (p → (q → r)) ↔ (p ∧ q → r) := by
  apply Iff.intro
  . by_contra h
    push_neg at h
    obtain ⟨h1, h2, h3⟩ := h
    obtain ⟨hp, hq⟩ := h2
    have h4 := by apply h1 hp hq
    contradiction
  . by_contra h
    push_neg at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    have h5 := by apply h1 (And.intro h2 h3)
    contradiction



/- EXERCISE 12
-/
example (p q r : Prop): ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := by
  apply Iff.intro
  . intro h
    constructor
    . by_contra h1
      push_neg at h1
      obtain ⟨h2, h3⟩ :=  h1
      have h4 := by apply h (Or.inl h2)
      contradiction
    . intro h5
      have h6 := by apply h (Or.inr h5)
      assumption
  . intro h
    obtain ⟨h7, h8⟩ := h
    by_contra h2
    push_neg at h2
    obtain ⟨h3, h4⟩ := h2
    apply Or.elim h3
    . intro hp
      have h5 := by apply h7 hp
      contradiction
    . intro hq
      have h6 := by apply h8 hq
      contradiction


/- EXERCISE 13
-/
example (p q: Prop): ¬(p ∨ q) ↔ ¬p ∧ ¬q := by
  apply Iff.intro
  . intro h
    push_neg at h
    obtain ⟨h1, h2⟩ := h
    constructor
    exact h1
    exact h2
  . intro h
    obtain ⟨h1, h2⟩ := h
    have h3 : ¬p ∧ ¬q := by
      constructor
      exact h1
      exact h2
    by_contra h4
    apply Or.elim h4
    . intro h5
      contradiction
    . intro h6
      contradiction








/- EXERCISE 14
-/
example (p: Prop): ¬(p ∧ ¬p) := by
  by_contra h
  obtain ⟨h1, h2⟩ := h
  contradiction


/- EXERCISE 15
-/
example (p q : Prop): p ∧ ¬q → ¬(p → q) := by
  intro h --We introduce the left hand side of the implication in the context
  push_neg --We push the not operator in the goal as much to the center as possible
  assumption --The hypothesis is identical with the goal, so it is an assumption of the goal.

/- EXERCISE 16
-/
example (p q : Prop): ¬p → (p → q) := by
  by_contra h
  push_neg at h
  obtain ⟨h1, h2, h3⟩ := h
  contradiction

/- EXERCISE 17
-/
example (p q : Prop): (¬p ∨ q) → (p → q) := by
  by_contra h
  push_neg at h
  obtain ⟨h1, h2, h3⟩ := h
  apply Or.elim h1
  . intro h4
    contradiction
  . intro h5
    contradiction




/- EXERCISE 18
-/
example (p : Prop): p ∨ False ↔ p := by
  constructor
  . intro h
    apply Or.elim h
    . intro hp
      assumption
    . intro hf
      contradiction
  intro h'
  apply Or.inl
  assumption





/- EXERCISE 19
-/
example (p : Prop): p ∧ False ↔ False := by
  constructor
  . intro h
    obtain ⟨h1, h2⟩ := h
    assumption
  . intro h
    constructor
    .contradiction
    .assumption



/- EXERCISE 20
-/
example (p q : Prop): (p → q) → (¬q → ¬p) := by
  by_contra h
  push_neg at h
  obtain ⟨h1, h2, h3⟩ := h
  have h4 := by exact h1 h3
  contradiction

/- EXERCISE 21
-/
example (p q r : Prop): (p → q ∨ r) → ((p → q) ∨ (p → r)) := by
  by_contra h
  push_neg at h
  obtain ⟨h1, h2, h3⟩ :=  h
  obtain ⟨h₂, h₂'⟩ := h2
  obtain ⟨h₃, h₃'⟩ := h3
  have h4 := by exact h1 h₂
  apply Or.elim h4
  . intro q
    contradiction
  . intro r
    contradiction


/- EXERCISE 22
-/
example (p q : Prop) : ¬(p ∧ q) → ¬p ∨ ¬q := by
  intro h
  push_neg at h
  by_cases hp : p
  . right
    exact h hp
  . left
    exact hp


/- EXERCISE 23
-/
example (p q : Prop) : ¬(p → q) → p ∧ ¬q := by
  intro h --We introduce the left hand side of the implication in the context
  push_neg at h --We push the not operator in the hypothesis previously introduced
  assumption --The result is that the hypothesis is exactly the goal. This is closed by assumption tactic.

/- EXERCISE 24
-/
example (p q : Prop) : (p → q) → (¬p ∨ q) := by
  intro h
  by_cases hp : p
  . right
    exact h hp
  . left
    exact hp


/- EXERCISE 25
-/


example (p q : Prop) : (¬q → ¬p) → (p → q) := by
  by_contra h
  push_neg at h
  obtain ⟨h1, h2, h3⟩ := h
  have h4 := by exact h1 h3
  contradiction



#check false_of_true_eq_false
#check false_imp_iff
-- variable (F : False)
-- #check F.elim
-- variable (p : Prop) (h1 : p) (h2 : ¬p)
-- #check False.elim (h2 h1)


/- EXERCISE 26
-/
example (p q : Prop) : (((p → q) → p) → p) := by
  by_contra h
  push_neg at h
  obtain ⟨h1, h2⟩ := h
  have hpq : p → q := fun hp => False.elim (h2 hp)
  have hp := h1 hpq
  -- exact h2 hp
  contradiction

example (n : ℕ) (h: n = 1 ∨ n = 2 ∨ n = 3) : n ≤ 3 := by
  rcases h with rfl | rfl | rfl <;> decide

example (x:ℝ) (h : ∃ x:ℝ, x ≥ 0) : x ≥ 1 := by
  obtain ⟨x, hx⟩ := h

example (p q :Prop) : q := by
  obtain ⟨hp | hnp⟩ := Classical.em p
