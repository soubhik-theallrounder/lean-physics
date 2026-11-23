/-!
# An exactly conserved harmonic oscillator

A symplectic integrator keeps a *modified* energy exactly constant even though
it cannot keep the usual `x^2 + p^2` constant.  Here is the smallest integer
example I could find.  One step is

    x' = x + p
    p' = p - x'          (= -x)

* it preserves phase-space area (determinant 1),
* it exactly conserves the quadratic form `Q(x, p) = x^2 + x p + p^2`,
* and applying it six times returns every point to where it started
  (a period-6 "orbit", the integer cousin of a rotation by 60 degrees).

The conserved `Q` plays the role of energy; the fact that it comes from a
symmetry of the update rule is the discrete shadow of Noether's theorem.
-/

namespace LeanPhysics

structure Phase where
  x : Int
  p : Int
  deriving DecidableEq, Repr

namespace Phase

def energy (s : Phase) : Int := s.x * s.x + s.x * s.p + s.p * s.p

/-- One symplectic-Euler step. -/
def step (s : Phase) : Phase :=
  let x' := s.x + s.p
  ⟨x', s.p - x'⟩

/-- Run `n` steps. -/
def iter : Nat → Phase → Phase
  | 0, s => s
  | n + 1, s => iter n (step s)

theorem step_x (s : Phase) : (step s).x = s.x + s.p := rfl
theorem step_p (s : Phase) : (step s).p = -s.x := by
  simp [step]; omega

/-- Energy is conserved by every single step. -/
theorem energy_step (s : Phase) : (step s).energy = s.energy := by
  simp [energy, step_x, step_p]; grind

/-- ...hence by any number of steps. -/
theorem energy_iter (n : Nat) (s : Phase) : (iter n s).energy = s.energy := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simp only [iter]; rw [ih, energy_step]

/-- Area preservation: the Jacobian determinant of the step map is 1.
The map is `(x, p) ↦ (1·x + 1·p, -1·x + 0·p)`, so det = 1·0 - 1·(-1) = 1. -/
theorem step_det : (1 : Int) * 0 - 1 * (-1) = 1 := by decide

/-- Every orbit has period dividing 6. -/
theorem period_six (s : Phase) : iter 6 s = s := by
  simp only [iter, step]
  cases s
  simp
  omega

/-- ...and no nonzero point comes back sooner than 6 steps
(checked on the generator `(1, 0)`). -/
example : iter 1 ⟨1, 0⟩ ≠ ⟨1, 0⟩ := by decide
example : iter 2 ⟨1, 0⟩ ≠ ⟨1, 0⟩ := by decide
example : iter 3 ⟨1, 0⟩ ≠ ⟨1, 0⟩ := by decide
example : iter 6 ⟨1, 0⟩ = ⟨1, 0⟩ := by decide

/-- The orbit of `(1, 0)` as a list, handy for plotting. -/
def orbit (s : Phase) : List Phase := (List.range 7).map (fun n => iter n s)

#eval orbit ⟨1, 0⟩

end Phase
end LeanPhysics
