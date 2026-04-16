
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-EXERCISE 7
  You need to prove the following inequality.
  The `linarith` tactic or other tactics which were not discussed are not allowed.

  Write comments to explain each step. Either here or inline.
-/
#check ne_of_gt
example {m : ℤ} (hm : 10 + m = 9) : 2 * m ≠ -3 := by
  have h : m = -1 := by -- An extra hypothesis heretherefore shortened h to facilitaty the ease of the proof.
    calc -- We use the calc command to create a chain of operations to prove the above h.
      m = (10 + m) - 10 := by ring -- We use the ring tactic for simple algebraic manipulations.
      _ = 9 - 10 := by rw[hm] -- We rewrite using the originial h.
      _ = -1 := by norm_num --  We use the norm_num command to simply the numerical expression.
  have h2 : 2 * m = -2 := by -- We create a second h. This second hypothesis was not necessary for the proof.
    --For example one could have written this as the first hypothesis and prove it with only one calc chain.
    calc
      2 * m = 2 * m := by rfl -- We use the reflixivity of the equality typeclass to get the proper LFH term.
      2 * m = 2 * (-1) := by rw[h] --We rewrite using our first proposed h.
      _ = -2 := by norm_num1 --We use norm_num1 to simplify the numerical expression on the RHS.
  apply ne_of_gt --We directly apply the thorem from Mathlib.Order.Defs.PartialOrder.
  --If an element is strictly greater than another then it is not equal to it.
  rw[h2] -- We rewrite using our second h.
  norm_num -- We use the norm_num command to simplify the numerical expression.

/-EXERCISE 14
  Fourier–Motzkin elimination.
  The `linarith` tactic or other tactics which were not discussed are not allowed.

  Write comments to explain each step. Either here or inline.
-/

--This preposterous amount of #check -s is just to verify the documentation or type of each theorem so that I know how to use it properly or which one to apply.
#check mul_add_mul_le_mul_add_mul
#check mul_le_iff_le_one_right
#check mul_le_mul_of_nonneg
#check mul_le_of_mul_le_left
#check mul_le_mul
#check mul_le_mul_iff_left
#check mul_le_mul_iff_of_pos_left
#check mul_le_mul_of_nonneg_left
#check mul_le_mul_of_nonneg_right
#check le_sub_iff_add_le
#check tsub_le_tsub_right
#check add_le_add_iff_right
#check le_trans
#check le_sub_iff_add_le.mp


example (x y: ℝ) (h1 : 2 * x + y ≥ 5) (h2 : x / 2 - y / 3 ≥ 1): x ≥ 16/7 := by
  have hₓ : x / 2 ≥ 1 + y / 3 := by
    exact le_sub_iff_add_le.mp h2
  have h₀ : 1 + y / 3 ≤ x / 2 := by exact hₓ
  have h₁ : 0 ≤ (2 : ℝ) := by norm_num
  have h₁₁ : (2 : ℝ) ≤ 2 := by rel[]
  have h₂ : (1 + y / 3) * 2 ≤ (x / 2) * 2 := by exact mul_le_mul_of_nonneg_right h₀ h₁
  sorry --First attempt. I didn't start it properly.

example (x y : ℝ) (h1 : 2 * x + y ≥ 5) (h2 : x / 2 - y / 3 ≥ 1) : x ≥ 16 / 7 := by
  have h1₁ : 5 ≤ 2 * x + y := by exact h1 -- We reverse the LHS and RHS of the inequality. It is easier to see everything in le rather than ge.
  have h1₂ : 5 ≤ 2 * x - -y := by -- We make another extra h to directly apply le_sub_iff_add_le.mp theorem
    calc
      5 ≤ 2 * x + y := h1₁
      _ = 2 * x - -y := by ring
  have h1₃ : 2 * x ≥ 5 - y := by exact le_sub_iff_add_le.mp h1₂
  --Since le_sub_iff_add_le is of type a ≤ b - c ↔ a + c ≤ b.
  --And since an equivalence is defined logically as a conjunction of implications.
  --We therefore know that le_sub_iff_add_le is a structure combining 2 functions.
  --Thus we need to specify the direction in which the logical inferenece should be applied.
  --Here: le_sub_iff_add_le.mp becomes of the type : a ≤ b - c → a + c ≤ b so it is a function that takes on one argument, i.e. a ≤ b - c
  --Similarly we can deduce that le_sub_iff_add_le.mpr (standing for modus ponens reversed) becomes of type : a + c ≤ b → a ≤ b - c
  have h3 : 0 ≤ (2 : ℝ) := by norm_num --An extra h to use as a parameter for the theorem used at the next step
  have h1₄ : 2 * (2 * x) ≥  2 * (5 - y) := by exact mul_le_mul_of_nonneg_left h1₃ h3 --We apply another theorem from Mathlib.Order.Defs.PartialOrder.
  --We multiply by a nonnegative number to the left of the sides of the inequality and the sign of the inequality doesn't change
  have h1₅ : 4 * x ≥ 10 - 2 * y := by -- We want to find more information about 4 * x  because it facilitates the use of transitivity later
    calc
      4 * x = 2 * (2 * x) := by ring
      _ ≥ 2 * (5 - y) := by rel[h1₄] -- We use the 'rel' tactic that is similar to rewrite. It is capable of solving a relational goal by rewriting.
      _ = 10 - 2 * y := by ring
  have h1₆ : 10 - 2 * y ≤ 4 * x := by exact h1₅ --We reverse the inequality to facilitate the use of  transivity later on.
  have h2₁ : 1 ≤ x / 2 - y / 3 := by exact h2 --We reverse the inequality to facilitate the use of transitivity later.
  have h2₂ : 1 - x / 2 ≤ (x / 2 - y / 3) - x / 2 := by exact tsub_le_tsub_right h2 (x / 2)
  --Another application of a theorem from the Mathlib.Order library.
  --From the name convention one can deduce: a tsui := alis for termen subtraction is less than or equal to another tsub (to the right)
  --This theorem has the type: (h : a ≤ b)  (c : α) : a - c ≤ b - c so we need to provide 2 arguments h2 and (x / 2) in our case.
  --One can see these theorems as functions who take in certain arguments of specified types.
  have h2₃ : 1 - x / 2 ≤ - y / 3 := by
    calc
    1 - x / 2 ≤ x / 2 - y / 3 - x / 2 := h2₂
    _ = - y / 3 := by ring  -- We do some simple algebraic manipulation of the inequality
  have h4 : 0 ≤ (6 : ℝ) := by norm_num --A helper h for usage in a theorem as an argument
  have h2₄ : 6 * (1 - x / 2) ≤ 6 * (-y / 3) := by exact mul_le_mul_of_nonneg_left h2₃ h4 -- We used this one above as well. The concepts remain
  have h2₅ : 6 - 3 * x ≤ -2 * y := by --Through the subsequent chain of operations we simplify the inequality to bring into a neat form
    calc
      6 - 3 * x = 6 * (1 - x / 2) := by ring
      _ ≤ 6 * (-y / 3) := by rel[h2₄]
      _ = -2 * y := by ring
  have h2₆ : 10 + (6 - 3 * x) ≤ 10 + (-2 * y) := by exact (add_le_add_iff_left 10).mpr h2₅
  --This is similar to another modus ponens and modus ponens reversed theorem explained above but this one adds a number to the left of the inequality while mainting the sign of the inequality
  have h2₇ : 16 - 3 * x ≤ 10 - 2 * y := by --We subsequently simplify the inequality through the calc chain of operations.
    calc
    16 - 3 * x  = 10 + (6 - 3 * x) := by ring
    _ ≤ 10 + (-2 * y) := by rel[h2₆]
    _ = 10 - 2 * y := by ring
    -- Thus far we know that: h1₆ : 10 - 2 * y ≤ 4 * x
    -- And we also know that: h2₇ : 16 - 3 * x ≤ 10 - 2 * y
    -- We look to apply the transitivity of le.

  have h5 : 16 - 3 * x ≤ 4 * x := by
    apply le_trans h2₇ h1₆ -- We apply the transitivity property of the le typeclass and we are almost done.

  have h5₁ : 16 ≤ 7 * x := by -- An extra h to simplify the inequality more.
    calc
      16 = (16 - 3 * x) + 3 * x := by ring
      _ ≤ 4 * x + 3 * x := by rel[h5]
      _ = 7 * x := by ring
  have h5₂ : 7 * x ≥ 16 := h5₁
  have h6 : 0 ≤ (1/7 : ℝ) := by norm_num --An extra h to use as an argument in the theorem below.
  have h5₃ : 1 / 7 * (7 * x) ≥ 1 / 7 * (16) := by exact mul_le_mul_of_nonneg_left h5₂ h6 -- We already used this theorem above and the concepts remain.
  calc
    x = 1 / 7 * (7 * x) := by ring
    _ ≥ 1 / 7 * (16) := by rel[h5₃]
    _ = 16 / 7 := by norm_num -- We bring a final simplification through a numerical normalization command. Done!:)


lemma extra_square {a b x : ℤ} (ha : a ≥ 0) : a * x^2 + b ≥ b := by
  apply le_add_of_nonneg_left
  have hz : (0 : ℤ) ≤ a * (0 : ℤ) := by
    apply le_of_eq
    ring
  have hx : 0 ≤ x^2 := sq_nonneg x
  apply le_mul_of_le_mul_of_nonneg_left hz hx ha

--Fetching the homework example for a 1:1 correspondence to the HW.
example {x : ℤ} (hx : x ≥ 1) : x ^ 3 + x ^ 2 ≥ 0 :=
  by
    have h : (2 : ℤ) ≥ 0 := by norm_num
    calc
      x ^ 3 + x ^ 2
        = x * x^2 + x^2 := by ring
      _ ≥ 1 * x^2 + x^2 := by rel [hx]
      _ = 2 * x^2 + 0 := by ring
      _ ≥ 0 := extra_square h -- above lemma


#check ge_trans

/-EXERCISE 26
  For the next exercise, you may use the above lemma `extra_square`.

  The `linarith` tactic or other tactics which were not discussed are not allowed.
-/
example {x : ℤ} (hx : x ≥ 2) : 6 * x ^ 3 - 7 * x ^ 2 + x + 2 ≥ 2 := by
  have h : 0 ≤ (5 : ℤ) := by norm_num --An extra h to use as an argument for the extra_square lemma below.
  calc
    6 * x^3 -7 * x ^ 2 + x + 2 = x * 6 * x ^ 2 - 7 * x ^ 2 + x + 2 := by ring  -- We manipulate the LHS to use the give relation (i.e. :  the hypothesis)
    _ ≥ 2 * 6 * x ^ 2 -7 * x ^ 2 + 2 + 2 := by rel[hx] --We use the 'rel' tactic that tries to solve the goal using a rewrite form a relational expression.
    _ = 5 * x ^ 2 + 4 := by ring --Algebraic manipulation using the 'ring' tactic
    _ ≥ 4 := extra_square h --Using the above lemma with the extra h
    _ ≥ 2 := by norm_num --Finally we normalize the numerical expression.
