import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-EXERCISE 4
  You need to prove the following equality using `calc` and `rw` and `ring`.
  The `linarith` tactic or other tactics which were not discussed are not allowed.

  Write comments to explain each step. Either here or inline.
-/
example (a b : ℝ) (h1 : 5 * a - 4 * b = 20) (h2 : b = 5) : a = 8 := by
  calc -- We use the 'calc' keyword that allows us to build a chain of calculations.
  --These calculations are in the form <expr 1> operand <expr 2> := by <proof>.
  --The operand could be any binary operation that is transitive like equality "=" or inequality "<=" for example.
    a = ((5 * a - 4 * b) + 4 * b) / 5 := by ring -- We use the ring tactic that automates algebraic manipulation of an expression long as the variables belong to certain algebraic structures.
    -- We rewrite the term 'a' using the hypotheses above so that it will facilitate the usage of a rewrite in furthur steps
    _ = ((20) + 4 * b) / 5 := by rw[h1] --We use 'rw' command that, as the name implies, rewrites the current goal using the hypothesis 'h1'.
    _ = ((20) + 4*5) / 5 := by rw[h2] --Likewise. We could have used the 'rewrite' keyword instead. The command 'rw' calls 'rfl' as well and tries to close the goal.
    _ = 8 := by norm_num -- We use the command 'norm_num' that normalizes numerical expressions, since all we have left is numerical type terms.

    /-EXERCISE 11
  You need to prove the following equality using `calc` and `rw` and `ring`.

  Write comments to explain each step. Either here or inline.
-/
example (x : ℝ) (hx : x ^ 2 - 4 = 0) : x^3 = 4 * x := by
  calc
    x^3 = x*(x^2 - 4) + 4*x := by ring
    _ = x*0 + 4*x := by rw[hx]
    _ = 4*x := by norm_num

/-EXERCISE 12
  You need to prove the following equality using `calc` and `rw` and `ring`.

  Write comments to explain each step. Either here or inline.
-/
example (x : ℝ) (hx : x ^ 2 - 1 = 0) :
  x^3 + 2 = x + 2 := by
    calc -- We use the 'calc' command which enables the user to structure a proof into a chain of equivalences, veritable to how a proof is jotted down on paper.
      x^3 + 2 = x*(x^2 - 1) + x +2 := by ring -- We use the ring tactic that allows for algebraic manipulation of an expression and we rewrite x^3 + 2 using the given hypothesis such that we can then rewrite it.
      _ = x*(0) + x + 2 := by rw[hx] -- We use 'rw' command to rewrite the goal of the proof using by replacing all the occurences of the hypothesis in the left-hand-side expression
      _ = x + 2 := by norm_num -- We use 'norm_num' command to deal with simplification/normalization of a numerical expression since we deal with terms of a numerical type.


/-EXERCISE 13
  You need to prove the following equality using `calc` and `rw` and `ring`.

  Write comments to explain each step. Either here or inline.
-/
example (x : ℝ) (hx : x ^ 2 - x = 0) :
  x^3 + 1 = x + 1 := by
    calc
    x^3 + 1 = x*(x^2 - x) + (x^2 - x) + x + 1 := by ring
    _ = x*0 + (x^2 - x) + x + 1 := by rw[hx]
    _ = x*(0) + 0 + x + 1 := by rw[hx]
    _ = x + 1 := by norm_num


/-EXERCISE 14
  You need to prove the following equality using `calc` and `rw` and `ring`.

  Write comments to explain each step. Either here or inline.
-/
example (x : ℝ) (hx : x ^ 2 - x = 0) :
  x^3 = x := by
    calc
    x^3 = x*(x^2 - x) + (x^2 - x) + x := by ring
    _ = x*(x^2 - x) + 0 + x := by rw[hx]
    _ = x*0 + 0 + x := by rw[hx]
    _ = x := by norm_num


/-EXERCISE 15
  You need to prove the following equality using `calc` and `rw` and `ring`.

  Write comments to explain each step. Either here or inline.
-/
example (x : ℝ) (hx : x ^ 2 - x + 1 = 0) :
  x^3 = -1 := by
    calc
      x^3 = x * (x^2 - x + 1) + (x^2 - x + 1) - 1 := by ring
      _ = x *(0) + 0 - 1 := by rw[hx]
      _ = -1 := by simp


/-EXERCISE 21
  You need to prove the following equality using `calc` and `rw`.
  The `ring` and `linarith` tactics are not allowed.

  Write comments to explain each step. Either here or inline.
-/
example (a b c d: ℝ):
  a * (b + c) * d = a * (c * d) + a * (b * d):= by
    calc
      a * (b + c) * d = (a * b + a * c) * d := by rw[mul_add]
      _ = a * b * d + a * c * d := by rw[add_mul]
      _ = a * c * d + a * b * d := by rw[add_comm (a*b*d) (a*c*d)]
      _ = a * (c * d) + a * (b * d) := by rw[mul_assoc, mul_assoc]

/-EXERCISE 22
  You need to prove the following equality using `calc` and `rw`.
  The `ring` tactic is not allowed.

  Write comments to explain each step. Either here or inline.
-/

-- Below are a few examples I exercised upon to get acquainted with these types of rewrites using associativiy, commutativity, and distribution.
#check mul_add
#check add_mul
#check mul_assoc
example (a b c : ℝ): a * b * c = b * (a * c) := by
  rw[mul_comm a b]
  rw[mul_assoc b a c]

example (a b c : ℝ) : a * (b * c) = b * a * c := by
  rw [<- mul_assoc a b c ]
  rw [mul_comm a b]

example (a b c d : ℝ) : a * (b + c) * d = (b + c) * (a * d) := by
  rw[mul_comm a  (b+c)]
  rw[mul_assoc (b+c) a d]

example (a b d : ℝ) : (a * b) * d = a * (b * d) :=by
  rw[mul_assoc]

example (a b d e : ℝ) : ((a * b) * d) * e = a * (b * d) * e := by
 calc
  ((a * b) * d) * e = (a * (b * d)) * e := by rw[mul_assoc a b d]
  _ = a * (b * d) * e := by rw[mul_assoc]

-- EXERCISE 22 solution
example (a b c d e: ℝ):
  a * (b + c) * d * e = a * (b * d) * e + a * (c * d) * e := by
    have h: a * (b + c) * d = a * b * d + a * c * d := by -- These kind of calculations tend to be a hindrance when done for the first time so I decided to make an intermediary lemma before continuing with the proof
    -- We use the 'have' keyword which is used to introduce intermediate facts (lemmas, subproofs, or definitions) inside a proof before continuing.
      calc
        a * (b + c) * d =  (a * b + a * c) *d := by rw[mul_add] --We rewrite using left distributivy that has the alias 'mul_add' which is intuitive since the first operand is multiplication and the second the addition.
        _ = a * b * d + a * c * d := by rw[add_mul] --Likewise, we rewrite the right-hand-expression using right distributivity which has the alias 'add-mul' for the same reasons as stated above.
    calc
      a * (b + c) * d * e  = (a * b * d + a * c * d) * e := by rw[h] -- Rewrite the expression using the intermediate lemma 'h'.
      _ = (((a * b) * d) * e) + (((a * c) * d) * e) := by rw[add_mul] -- Lean always tries to put the parantheses as much to the left as possible. We keep that in mind and rewrite the expresion using distributivity.
      _ = (a * (b * d)* e) + (a* (c * d) * e) := by rw [mul_assoc a b d, mul_assoc a c d] -- We rearange the parantheses using the 'mul_assoc' lemma. Which states that for three variable a,b,c and that belong to at least a Semigroup then a*b*c = a*(b*c) which Lean sees as (a*b)*c = a*(b*c)
      _ = a * (b * d) * e + a * (c * d) * e := by rw[mul_assoc, mul_assoc] --Similarly, we get rid of the extra parantheses using the 'mul_assoc' lemma since all our variable belong to more than a Semigroup and thus have satisfy the associativity lemma.

/-EXERCISE 23
  You need to prove the following equality using `calc` and `rw`.F
  The `ring` tactic is not allowed.

  Write comments to explain each step. Either here or inline.
-/
example (a b c d e : ℝ) :
  a * (b * c) * d * e = (a * e) * (b * (c * d)) := by
    calc
      a * (b * c) * d * e = a * (b * c) * (d * e) := by rw[mul_assoc (a*(b*c)) d e ]
      _ = a * (b * c) * (e * d) := by rw[mul_comm e d]
      _ = a * (b * c) * e * d := by rw[<-mul_assoc]
      _ = a * ((b * c) * e) * d := by rw[mul_assoc a (b * c) e]
      _ = a * (e * (b * c)) * d := by rw[mul_comm (b *c) e]
      _ = (a * e) * (b * c) * d := by rw[<-mul_assoc a e (b*c)]
      _ = (a * e) * ((b * c) * d) := by rw[mul_assoc (a * e) (b * c) d]
      _ = (a * e) * (b * (c * d)) := by rw[mul_assoc b c d]


/-EXERCISE 24
  You need to prove the following equality using `calc` and `rw`.
  The `ring` tactic is not allowed.

  Write comments to explain each step. Either here or inline.
-/
example (a b c d: ℝ):
  (a + b) * c * d = c * d * a + b * (c * d)  := by
    calc
    (a + b) * c * d = (a * c + b * c) * d := by rw[add_mul]
    _ = (a * c * d) + (b * c * d) := by rw[add_mul]
    _ = (c * a * d) + (b * c * d) := by rw[mul_comm a c]
    _ = (c * (a * d)) + (b * c * d) := by rw[mul_assoc]
    _ = (c * (d * a)) + (b * c * d) := by rw[mul_comm a d]
    _ = (c * d * a) + (b * c * d) := by rw[<-mul_assoc]
    _ = (c * d *a) + (b * (c * d)) := by rw[mul_assoc b c d]


/-EXERCISE 25
  You need to prove the following equality using `calc` and `rw`.
  The `ring` tactic is not allowed.

  Write comments to explain each step. Either here or inline.
-/
example (a b c d e: ℝ):
  (a + b) * c * ( d + e ) = a * c * d + b * c * d + (a * c * e + e * (b * c)) := by
    calc
    (a + b) * c * (d + e) = (a * c + b * c) * (d + e) := by rw[add_mul]
    _ = (a * c + b * c) * d + (a * c + b * c) * e := by rw[mul_add]
    _ = ((a * c) * d) + ((b * c) * d) + (a * c + b * c) * e := by rw[add_mul]
    _ = ((a * c) * d) + ((b * c) * d) + (((a * c) * e) + ((b * c) * e)) := by rw[add_mul]
    _ = ((a * c) * d) + ((b * c) * d) + (((a * c) * e) + (e * (b * c))) := by rw[mul_comm e (b*c)]


example {α β : Type} (h : α = β) (x : α) : β := cast h x
