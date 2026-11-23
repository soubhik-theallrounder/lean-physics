import LeanPhysics.SplitComplex
import LeanPhysics.Oscillator
import LeanPhysics.Heisenberg
import LeanPhysics.Galilean
import LeanPhysics.FreeFall

open LeanPhysics

-- Sanity check: none of the main results depend on `sorry`.
#print axioms Event.interval_mul
#print axioms Event.boost_preserves_interval
#print axioms Phase.energy_iter
#print axioms Phase.period_six
#print axioms commutator
#print axioms number_commutes
#print axioms GEvent.boost_add
#print axioms GEvent.simultaneous_distance
#print axioms Fall.run_x
#print axioms Fall.work_energy
