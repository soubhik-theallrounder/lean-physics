/-!
# Minkowski spacetime as split-complex numbers

In 1+1 dimensions (units with c = 1) an event is a pair (t, x).  Packaging it as
the split-complex number `t + x·j`, with `j * j = 1`, makes Lorentz boosts
nothing more than multiplication, and the spacetime interval becomes the norm
`t^2 - x^2`.

Everything here is over `Int` so that the statements are exact (no real numbers,
no Mathlib).  A boost with "rapidity data" `(a, b)` scales the interval by
`a^2 - b^2`; boosts with `a^2 - b^2 = 1` preserve it exactly.
-/

namespace LeanPhysics

/-- A 1+1 dimensional event / split-complex number `t + x j` with `j^2 = 1`. -/
structure Event where
  t : Int
  x : Int
  deriving DecidableEq, Repr

namespace Event

/-- Spacetime interval, signature (+,-). -/
def interval (e : Event) : Int := e.t * e.t - e.x * e.x

/-- Split-complex multiplication, `(a + b j)(c + d j) = (ac + bd) + (ad + bc) j`. -/
def mul (p q : Event) : Event := ⟨p.t * q.t + p.x * q.x, p.t * q.x + p.x * q.t⟩

instance : Mul Event := ⟨mul⟩

def one : Event := ⟨1, 0⟩

@[simp] theorem mul_t (p q : Event) : (p * q).t = p.t * q.t + p.x * q.x := rfl
@[simp] theorem mul_x (p q : Event) : (p * q).x = p.t * q.x + p.x * q.t := rfl

theorem ext' {p q : Event} (h1 : p.t = q.t) (h2 : p.x = q.x) : p = q := by
  cases p; cases q; simp_all

theorem mul_comm (p q : Event) : p * q = q * p := by
  apply ext' <;> simp <;> grind

theorem mul_assoc (p q r : Event) : (p * q) * r = p * (q * r) := by
  apply ext' <;> simp <;> grind

theorem one_mul (p : Event) : one * p = p := by
  apply ext' <;> simp [one]

/-- The interval is multiplicative: the "Lorentz factor" of a product is the
product of the factors.  This is the key algebraic fact behind everything below. -/
theorem interval_mul (p q : Event) :
    (p * q).interval = p.interval * q.interval := by
  simp [interval]; grind

/-- A boost is multiplication by a fixed event. -/
def boost (b e : Event) : Event := b * e

/-- Boosts with unit norm preserve the interval exactly. -/
theorem boost_preserves_interval (b e : Event) (hb : b.interval = 1) :
    (boost b e).interval = e.interval := by
  unfold boost
  rw [interval_mul, hb, Int.one_mul]

/-- Composing two boosts is the same as boosting by the product. -/
theorem boost_comp (b c e : Event) : boost b (boost c e) = boost (b * c) e := by
  unfold boost
  rw [mul_assoc]

/-- Causal character of an interval. -/
inductive Causal | timelike | spacelike | lightlike
  deriving DecidableEq, Repr

def causal (e : Event) : Causal :=
  if e.interval > 0 then .timelike
  else if e.interval < 0 then .spacelike
  else .lightlike

/-- Light-like events stay light-like under any boost with unit norm:
the light cone is invariant, which is the whole content of "c is the same for
every observer" in this toy model. -/
theorem lightcone_invariant (b e : Event) (hb : b.interval = 1) :
    e.interval = 0 → (boost b e).interval = 0 := by
  intro h
  rw [boost_preserves_interval b e hb, h]

/-- Causal character is preserved by unit boosts. -/
theorem causal_invariant (b e : Event) (hb : b.interval = 1) :
    (boost b e).causal = e.causal := by
  simp only [causal, boost_preserves_interval b e hb]

/-- Over the integers the only unit-norm split-complex numbers have zero spatial
part: `(a - b)(a + b) = 1` forces `a - b = ±1`, `a + b = ±1`. -/
theorem unit_norm_trivial (a b : Int) (h : a * a - b * b = 1) : b = 0 := by
  have h2 : (a - b) * (a + b) = 1 := by grind
  have h3 : (a - b).natAbs * (a + b).natAbs = 1 := by
    rw [← Int.natAbs_mul, h2]; rfl
  have h4 := Nat.eq_one_of_mul_eq_one_right h3
  have h5 := Nat.eq_one_of_mul_eq_one_left h3
  have e1 : a - b = 1 ∨ a - b = -1 := by omega
  have e2 : a + b = 1 ∨ a + b = -1 := by omega
  -- the signs must agree because the product is +1
  rcases e1 with e1 | e1 <;> rcases e2 with e2 | e2 <;>
    (rw [e1, e2] at h2; first | omega | simp at h2 | skip) <;> omega

/-- Worked example: the event (5, 3) is timelike with interval 16. -/
example : (Event.mk 5 3).interval = 16 := by decide
example : (Event.mk 5 3).causal = Causal.timelike := by decide

/-- Over the integers the only unit-norm "boosts" are the trivial ones `±1`
(there are no integer points on the hyperbola `a^2 - b^2 = 1` with `b ≠ 0`),
which is why `interval_mul`, the scaled statement, is the useful one here. -/
example : (Event.mk (-1) 0).interval = 1 := by decide

end Event
end LeanPhysics
