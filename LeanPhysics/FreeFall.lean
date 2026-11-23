/-!
# Free fall with a discrete clock

Constant acceleration `g` stepped with semi-implicit Euler:

    v' = v + g
    x' = x + v'

The exact solution is the school formula `x_n = x_0 + n v_0 + g n (n+1) / 2`.
To stay inside `Int` the position formula is stated doubled:
`2 x_n = 2 x_0 + 2 n v_0 + g n (n+1)`.  The discrete work-energy identity
(`work_energy`) carries a small `g^2 n` correction, which is the price of the
finite time step.
-/

namespace LeanPhysics

structure Fall where
  x : Int
  v : Int
  deriving DecidableEq, Repr

namespace Fall

def step (g : Int) (s : Fall) : Fall :=
  let v' := s.v + g
  ⟨s.x + v', v'⟩

def run (g : Int) : Nat → Fall → Fall
  | 0, s => s
  | n + 1, s => step g (run g n s)

theorem run_v (g : Int) (s : Fall) (n : Nat) : (run g n s).v = s.v + n * g := by
  induction n with
  | zero => simp [run]
  | succ k ih => simp [run, step, ih]; grind

/-- Doubled position formula. -/
theorem run_x (g : Int) (s : Fall) (n : Nat) :
    2 * (run g n s).x = 2 * s.x + 2 * n * s.v + g * n * (n + 1) := by
  induction n with
  | zero => simp [run]
  | succ k ih =>
    simp only [run, step, run_v]
    grind

/-- Work-energy theorem for the discrete clock:
`v_n^2 - v_0^2 = 2 g (x_n - x_0) - g^2 n`. -/
theorem work_energy (g : Int) (s : Fall) (n : Nat) :
    (run g n s).v * (run g n s).v - s.v * s.v
      = 2 * g * ((run g n s).x - s.x) - g * g * n := by
  have hx := run_x g s n
  have hv := run_v g s n
  rw [hv]
  grind

/-- Dropped from rest at the origin with g = 10: after 3 ticks, x = 60, v = 30. -/
example : run 10 3 ⟨0, 0⟩ = ⟨60, 30⟩ := by decide

end Fall
end LeanPhysics
