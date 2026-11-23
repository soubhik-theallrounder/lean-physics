/-!
# Galilean relativity, exactly

Before Lorentz there was Galileo.  A Galilean boost with velocity `v` sends an
event `(t, x)` to `(t, x + v t)`.  Over `Int` we can prove the textbook facts
exactly:

* boosts compose by *adding* velocities,
* boosts with `v = 0` do nothing, and every boost has an inverse (so they form a group),
* time is absolute, and the distance between two *simultaneous* events is invariant.

Compare with `SplitComplex.lean`, where velocities no longer simply add.
-/

namespace LeanPhysics

structure GEvent where
  t : Int
  x : Int
  deriving DecidableEq, Repr

namespace GEvent

/-- Galilean boost by velocity `v`. -/
def boost (v : Int) (e : GEvent) : GEvent := ⟨e.t, e.x + v * e.t⟩

theorem boost_zero (e : GEvent) : boost 0 e = e := by
  cases e; simp [boost]

/-- Velocities add. -/
theorem boost_add (v w : Int) (e : GEvent) : boost v (boost w e) = boost (v + w) e := by
  cases e; simp [boost]; grind

theorem boost_neg (v : Int) (e : GEvent) : boost (-v) (boost v e) = e := by
  rw [boost_add, show -v + v = 0 by omega, boost_zero]

/-- Time is absolute. -/
theorem time_absolute (v : Int) (e : GEvent) : (boost v e).t = e.t := rfl

/-- Distance between simultaneous events does not depend on the observer. -/
theorem simultaneous_distance (v : Int) (a b : GEvent) (h : a.t = b.t) :
    (boost v a).x - (boost v b).x = a.x - b.x := by
  simp [boost, h]; grind

/-- The speed of a worldline `x = u t` shifts by exactly `v`. -/
theorem velocity_shift (u v t : Int) :
    (boost v ⟨t, u * t⟩).x = (u + v) * t := by
  simp [boost]; grind

end GEvent
end LeanPhysics
