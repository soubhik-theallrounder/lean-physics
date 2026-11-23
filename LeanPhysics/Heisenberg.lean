/-!
# The Heisenberg commutation relation `[a, a†] = 1`

Quantum states of a harmonic oscillator live on the occupation numbers
n = 0, 1, 2, ...  I model a state as a function `Nat → Int` giving the
coefficient of the n-th basis vector (unnormalised, so there are no square
roots).  With

    (a† f)(n) = f(n-1)        for n ≥ 1,   (a† f)(0) = 0
    (a  f)(n) = (n+1) f(n+1)

the commutator `a a† - a† a` is exactly the identity.  This is the
Weyl-Heisenberg algebra behind creation and annihilation operators and, with a
little more work, the uncertainty principle.

The number operator `N = a† a` then satisfies `[N, a†] = a†`, i.e. applying
`a†` raises the number of quanta by one.
-/

namespace LeanPhysics

abbrev State := Nat → Int

/-- Creation operator. -/
def create (f : State) : State
  | 0 => 0
  | n + 1 => f n

/-- Annihilation operator. -/
def annihilate (f : State) : State :=
  fun n => ((n : Int) + 1) * f (n + 1)

/-- Number operator `N = a† a`. -/
def number (f : State) : State := create (annihilate f)

theorem create_zero (f : State) : create f 0 = 0 := rfl
theorem create_succ (f : State) (n : Nat) : create f (n + 1) = f n := rfl

/-- The canonical commutation relation: `a (a† f) - a† (a f) = f`. -/
theorem commutator (f : State) (n : Nat) :
    annihilate (create f) n - create (annihilate f) n = f n := by
  cases n with
  | zero =>
      simp [annihilate, create]
  | succ k =>
      simp [annihilate, create]
      grind

/-- Applying `a†` to the vacuum `e₀ = (1, 0, 0, ...)` gives `e₁`. -/
def basis (k : Nat) : State := fun n => if n = k then 1 else 0

theorem create_basis (k : Nat) : create (basis k) = basis (k + 1) := by
  funext n
  cases n with
  | zero => simp [create, basis]
  | succ m => simp [create, basis]

/-- The vacuum is annihilated: `a e₀ = 0`. -/
theorem annihilate_vacuum : annihilate (basis 0) = fun _ => 0 := by
  funext n
  simp [annihilate, basis]

/-- `N e_k = k e_k`: the number operator counts quanta. -/
theorem number_basis (k : Nat) : number (basis k) = fun n => (k : Int) * basis k n := by
  funext n
  cases n with
  | zero =>
      cases k <;> simp [number, create, basis]
  | succ m =>
      simp only [number, create, annihilate, basis]
      by_cases h : m = k - 1 <;> by_cases hk : k = 0 <;> grind

/-- `[N, a†] = a†`, i.e. `a†` raises the occupation number by exactly one. -/
theorem number_commutes (f : State) (n : Nat) :
    number (create f) n - create (number f) n = create f n := by
  cases n with
  | zero => simp [number, create]
  | succ k =>
      cases k with
      | zero => simp [number, create, annihilate]
      | succ j => simp [number, create, annihilate]; grind

end LeanPhysics
