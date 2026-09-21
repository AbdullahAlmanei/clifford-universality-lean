import TwoControl.Clifford.Universal.MainTheorem

open Matrix

namespace TwoControl
namespace Top100

open Clifford.Universal

/-- **Distance-independent universality of quantum gate sets (#41).**

For every finite number of qubits, every unitary operation, and every positive
error tolerance, a finite circuit of embedded CNOT, Hadamard, and `T` gates
approximates the operation for every projective distance satisfying the four
laws isolated in `ProjectiveDistanceMeasure`.
-/
theorem clifford_t_is_an_approximately_universal_quantum_gate_set {n : ℕ}
    (d : ProjectiveDistanceMeasure (2 ^ n))
    (U : Square (2 ^ n))
    (hU : U ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ gates : List (Square (2 ^ n)),
      CircuitOver (CliffordTGate n) gates ∧
        d U (circuitMatrix gates) < ε :=
  clifford_t_is_universal_projective d U hU hε

/-- The Top 100 statement specialized to projective Hilbert--Schmidt
distance, whose satisfaction of the four abstract laws is proved in Lean. -/
theorem clifford_t_is_an_approximately_universal_quantum_gate_set_hs {n : ℕ}
    (U : Square (2 ^ n))
    (hU : U ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ gates : List (Square (2 ^ n)),
      CircuitOver (CliffordTGate n) gates ∧
        hsDistance U (circuitMatrix gates) < ε :=
  clifford_t_is_universal_hs_via_projective U hU hε

end Top100
end TwoControl
