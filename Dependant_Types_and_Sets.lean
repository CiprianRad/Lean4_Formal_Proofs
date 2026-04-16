import Mathlib.Data.Set.Basic
import Mathlib.Tactic

/- EXERCISE 3
  prove or disprove
-/

#check Int.sub_lt_sub_right_iff
example : {m : ℤ | m ≥ 10} ⊆ {n : ℤ | n ^ 3 - 7 * n ^ 2 ≥ 4 * n} := by
  dsimp [Set.subset_def] -- We take an element for the lhs set and want to show it is in the rhs set
  intro x hx -- Since that element is arbitrarly chosen, we introduce the universal quantifier along with the predicate it satisfies to be in the lhs set
  have h :=
    calc -- We tranform the inequality in the goal to get to the needed upper bound
      x ^ 3 - 7 * x ^ 2 - 4 * x = x * x ^ 2 - 7 * x ^ 2 - 4 * x := by ring
      _ ≥ 10 * x ^2 - 7 * x ^ 2 - 4 * x := by rel[hx]
      _ = x * 3 * x - 4 * x := by ring
      _ ≥ 10 * 3 * x - 4 * x := by rel[hx]
      _ = 26 * x := by ring
      _ ≥ 26 * 10 := by rel [hx]
      _ = 260 := by norm_num
      _ ≥ 0 := by exact Int.zero_le_ofNat 260
  exact Int.sub_nonneg.mp h --We bring the inequality above to the one in the goal by subtraction with non negative number


variable {α β : Type*}
variable (f : α → β)
variable (s t : Set α)
variable (u v : Set β)

open Function
open Set

/- EXERCISE 13
-/
#check Set.inter_def
#check mem_setOf

example : s ∩ (s ∪ t) = s := by
  ext x --We use the extensionality principles and transform the equality into a logical equivalence
  constructor --We construct iff with 2 implication
  . intro h --We introduce the lhs of the implication
    obtain ⟨h1, h2⟩ := h -- `x` is in the intersection therefore is in both
    exact h1 --We only care that is is in `s`
  . intro h --We introduce the lhs of the implication
    rw [mem_inter_iff] --For x to be in an intersection it need to be in both, so we rewrite it into a disjunction
    constructor --We construct the disjunction
    . exact h  --For lhs we care only that x ∈ s
    . exact mem_union_left t h  --For x ∈ s ∪ t it sufficies to show that x ∈ s

/- EXERCISE 26
-/
theorem inter_img_subset_img_inter_of_inj (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  intro x h1 --For `every` x in the intersection of images we need to show it is in the image of intersection
  obtain ⟨h2, h3⟩ := h1 -- `x` is in intersection, therefore it is in both
  obtain ⟨y, hy⟩ := h2 -- `x`  is in image through s, therefore there is a y : α, y ∈ s such that f y = x
  obtain ⟨z, hz⟩ := h3 --ibidem for the image through t
  obtain ⟨ys, fyx⟩ := hy --We split the disjunction
  obtain ⟨zt, fzx⟩ := hz --Ibidem
  have hfyz : f y = f z := by exact Eq.trans fyx (Eq.symm fzx) --Since f y = x and f z = x it implies f y = f z
  have hyz : y = z := by exact h hfyz --Since f is Injective it implies that y = z
  have h' : y  ∈ s ∩ t := by subst hyz; exact ⟨ys, zt⟩ --Since y = z, y ∈ s and z ∈ t -> y ∈ s ∩ t
  use y

theorem img_inter_subset_inter_img : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  intro x hx
  obtain ⟨y, hy⟩ := hx
  obtain ⟨h1, fyx⟩ := hy
  obtain ⟨ys, yt⟩ := h1
  constructor
  . use  y
  . use  y

theorem img_inter_eq_inter_img_of_inj (h : Injective f) : f '' s ∩ f '' t = f '' (s ∩ t) := by
  apply Set.Subset.antisymm
  · exact inter_img_subset_img_inter_of_inj (f := f) (s := s) (t := t) h
  · exact img_inter_subset_inter_img (f := f) (s := s) (t := t)
