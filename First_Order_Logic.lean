import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/- EXERCISE 3
    Find the solutions of the system,
    replace the correct values for `x` and `y` and
    complete the proof of the statement

    The `linarith` tactic or other tactics which were not discussed are not allowed.
    Write comments to explain each step. Either here or inline.
-/
example : ∀ x y : ℝ, 5 * x + 2 * y = 3 ∧ 3 * x - 4 * y = 2 → x = 8 / 13 ∧ y = -1/26 :=
    by
        intro x y h --We introduce the universal quantifier variables and the logical proopositions in our context with the keyword intro, turning them inot hypothesis for our context
        obtain ⟨h1, h2⟩ := h --We use the `obtain` tactic that uses `have` and `recursive cases` to infer the type of the hypothesis in the angular brackets and construct them from the hypothesis in the form of a conjunction
        have hx : x = 8 / 13 := by --A intermediate hypothesis
            calc
                x = ((2 * (5 * x + 2 * y)) + (3 * x - 4 * y)) / 13 := by ring --Using the `ring` tactic for algebraic manipulation
                _ = ((2 * 3) + 2) / 13 := by rw[h1, h2] --Rewriting the hypothesis into the current goal
                _ = 8 / 13 := by norm_num --Simplifying the numerical expression with `norm_num` tactic
        have hy : y = -1/26 := by --Intermediate hypothesis. We prove it similarly to the one above
            calc
                y = (5 * x + 2 * y) + (1 / 4) * (3 * x - 4 * y) - (23 / 4) * x:= by ring
                _ = (3) + (1/4) * (2) - 23 / 4 * x := by rw[h1, h2]
                _ = 7 / 2 - (23 / 4) * x := by norm_num
                _ = 7 / 2 - (23 / 4) * (8 / 13) := by rw[hx]
                _ = -1 / 26 := by norm_num1
        constructor --We split the goal which is a conjunction into 2 cases using the `constructor` keyword. We then prove the 2 goals
        . exact hx
        . exact hy


/- EXERCISE 12
    Find the solutions of the quadratic equation,
    replace the correct values for `x` and
    complete the proof of the statement

    The `linarith` tactic or other tactics which were not discussed are not allowed.
    Write comments to explain each step. Either here or inline.
-/

#check mul_eq_zero
#check zero_eq_mul

example : ∀ x : ℝ, 3 * x ^ 2 + 13 * x - 10 = 0 → x = -5 ∨ x = 2/3 := by
    intro x h --We introduce the variables and hypothesis into the current context using the `intro` tactic like in the previous problem
    have h₁ : (x + 5) * (x - 2 / 3) = 0 := by --We factor out the quadratic into a product.
        calc
            (x + 5) * (x - 2 / 3) = (3 * x ^ 2 + 13 * x - 10) / 3 := by ring -- We make algebraic manipulation of with the `ring` tactic
            _ =  0 / 3 := by rw[h] --Rewrite hypothesis h in the current goal
            _ = 0 := by norm_num1 --Simplify the numerical expression

    have h₂ : (x + 5 = 0) ∨ (x - 2 / 3 = 0) := by exact mul_eq_zero.mp h₁ --A intermediate hypothesis we obten by applying the theorem mul_eq_zero.mp from Mathlib.Algebra.GroupWithZero.Defs
    -- We know that in a group with zero that has no divisors of 0, a*b=0 implies a=0 or b=0. The theorem above states that fact

    obtain hₓ1 | hₓ2 := h₂ --We once again use the `obtain` tactic to divide the conjunction into 2 propositions which we'll then use to construct the goal.
    left  --We prove the first constructor of the conjunction we have as a goal (i.e the left hand proposition)
    calc
        x = (x + 5) - 5 := by ring
        _ = 0 - 5 := by rw[hₓ1]
        _ = -5 := by norm_num1

    right --Likewise we consider separately the right hand term of the conjunction we need to prove. This is the second constructor for the conjunction
    calc
        x = (x - 2 / 3) + 2 / 3 := by ring
        _ = 0 + 2 / 3 := by rw[hₓ2]
        _ = 2 / 3 := by norm_num1

/-EXERCISE 30
    Fourier–Motzkin elimination.

    The `linarith` tactic or other tactics which were not discussed are not allowed.
    Write comments to explain each step. Either here or inline.
-/

#check mul_le_mul
#check mul_le_mul_left_of_neg
#check mul_le_mul_of_nonpos_left
#check le_trans

--Slight refactorization of the last problem

example : ∀ x y: ℝ, - x / 2 + 2 * y ≥ 5 ∧ x + y / 3 ≥ 2 → y ≥ 1/52 := by
    intro x y h --We introduce the variables x and y in the current context as well as the conjunction in the form of the hypothesis
    obtain ⟨h1, h2⟩ := h --We divide the conjunction hypothesis (labeled h) into two separate hypothesis(labeled h1 and h2) using the `obtain` tactic

    have hₓ1 :=  by --An intermediate hypothesis to simplify h1
        calc
            -x + 4 * y = 2 * (- x / 2 + 2 * y) := by ring
            _ ≥ 2 * 5 := by rel[h1]
            _ = 10 := by norm_num1

    have hx₂ := by --Another intermediat hypothesis to simplify hₓ1
        calc
            -x = (-x + 4 * y) - 4 * y := by ring
            _ ≥ 10 - 4 * y := by rel[hₓ1]

    have h3 : (-1 : ℝ) ≤ 0 := by norm_num --A hypothesis we use to apply the theorem below

    have hx₃:= by
        calc
            x = (-1) * (-x) := by ring
            _ ≤ (-1) * (10 - 4 * y ) := by exact mul_le_mul_of_nonpos_left hx₂ h3
            --We used a theorem from Mathlib.Algebra.Order.Ring.Unbundled.Basic
            --It states than in a Semiring with a Preorder if we multiply to the left with a negative number the direction of the inequality changes.
            _ = 4 * y - 10 := by ring

    have hx₄ := by --We don't need to explictly tell what the hypothesis is, Lean automatically infers it to be the last equivalence in the calc chain
        calc
            x = (x + y / 3) - y / 3 := by ring
            _ ≥ 2 - y / 3 :=  by rel[h2]

    have hy : 2 - y / 3 ≤ 4 * y - 10 := by exact le_trans hx₄ hx₃ --We apply transitivity to get rid of the `x` variable such that we'll have an inequality only in terms of `y`

    have hy₁ := by --We manipulate the inequality to get to a proper form
        calc
            12 =(((2 - y / 3) + y / 3) + 10) := by ring
            _ ≤ (4 * y - 10 + y / 3 + 10) := by rel[hy]
            _ = 13 / 3 * y := by ring

    have hy₂ : 13 / 3 * y ≥ 12 := hy₁ --We invert it to match the goal

    calc --A final calc chain that proves the goal
        y = 3 / 13 * (13 / 3 * y) := by ring
        _ ≥ 3 / 13 * (12) := by rel[hy₁]
        _ ≥ 1/52 := by norm_num1

/- OTHER EXERCISES
   Similar to Exercises 1-3 from 2.1 of https://hrmacbeth.github.io/math2001/02_Proofs_with_Structure.html#intermediate-steps
-/


#check Rat.mul_div_cancel

example : ∀ x : ℚ, x ^ 2 = 4 → 1 < x → x = 2 := by
    intro x h1 h2 -- We introduce the variable and the two logical statements in the contest as hypothesis
    have h3 := --To show that x = 2 we prove that `x * (x + 2) = 2 * (x + 2)` such that we can then `cancel out (x + 2)`
        calc
            x * (x + 2) = x ^ 2 + 2 * x := by ring
            _ = 4 + 2 * x := by rw[h1]
            _ = 2 * (x + 2) := by ring
    have h4 : x + 2 > 0 := by
        calc
            x + 2 > 1 + 2 := by rel[h2]
            _ = 3 := by norm_num1
            _ > 0 := by norm_num1
    have h5 : x + 2 ≠ 0 := by exact ne_of_gt h4 --To cancel out with x+2 we first prove it is different than 0 using the hypothesis that x > 1
    calc
        x = (x * (x + 2)) / (x + 2) := by exact Eq.symm (Rat.mul_div_cancel h5)
        -- If we divide and multiply by a non-null number then the result is the same expression.
        -- Rat.mul_div_cancel from Init.Data.Rat.Lemmas states that fact.
        _ = (2 * (x + 2)) / (x + 2) := by rw[h3] --We rewrite h3 in the current goal.
        _ = 2 := by exact Rat.mul_div_cancel h5 --We apply the Lemma to resimplify it



example : ∀ n : ℤ, n ^ 2 + 4 = 4 * n → n = 2 := by
    intro n h --We introduce the variables and hypothesis into the current context with the `intro` tactic
    have h1 := by
        calc
            (n - 2) ^ 2 = (n ^ 2 + 4) - 4 * n  := by ring
            _ =  4 * n - 4 * n := by rw[h]
            _ = 0 := by simp  --We get the quadratic into the right form to apply mul_eq_zero
    have h2 : ((n - 2) ^ 1 = 0) ∨ (n - 2=0)  := by exact mul_eq_zero.mp h1
    --We use the mul_eq_zero lemma that states that if a product of 2 terms is zero then either one is zero or the other(in the case of groups with zero that have no 0 divisors)
    --It is a logical equivalence so we specify the direction of the implication with `mp`
    obtain hₙ1 | hₙ2 := h2 --We split the hypothesis in two and this splits the goal in 2 cases in which the hypothesis on the left is true and when the one on the right is true (case inl, casse inr)
    · calc --Proving for the left hand side hypothesis as true
      n = (n - 2) ^ 1 + 2 := by ring
      _ = 0 + 2 := by rw[hₙ1]
      _ = 2 := by simp
    · calc --Proving for the right hand side hypothesis as true
      n = (n - 2) + 2 := by ring
      _ = 0 + 2 := by rw[hₙ2]
      _ = 2 := by simp


#check div_le_one₀

example : ∀ x y : ℚ, x * y = 1 → x ≥ 1 → y ≤ 1 := by
    intro x y h1 h2 --Placing the variables and implications as hypothesis in the current context using the `intro` tactic
    have h3 : x > 0 := by
        calc
            x ≥ 1 := h2
            _ > 0 := by exact rfl
    have h4 : x ≠ 0 := by exact ne_of_gt h3 --We prove that x is not equal to zero to use the lemma bellow
    calc
        y = y * x / x := by exact Eq.symm (Rat.mul_div_cancel h4)
        _ = x * y / x := by ring
        _ = 1 / x := by rw[h1]
        _ ≤ 1 := by exact (div_le_one₀ h3).mpr h2
    --We apply `div_le_one₀` - a lemma for usage in Groups with zero that have a partial order
    --It is applied on the hypothesis that a number is greater than zero and it works on a logical equivalence so the direction of the implication is specified with `mp` or `mpr`
    --It states that if 0 < b then a / b ≤ 1 <-> a ≤ b
