import TwoControl.Clifford.Universal.Distance
import TwoControl.Clifford.Universal.ProjectiveMainTheorem
import TwoControl.Clifford.Universal.RzApproximation

namespace TwoControl
namespace Clifford
namespace Universal

/-!
# Clifford+T universality for Hilbert--Schmidt distance

The distance-independent proof lives in `ProjectiveMainTheorem`. This module
instantiates it with the projective Hilbert--Schmidt distance and preserves the
original public theorem name.
-/

/-- Clifford+T universality for projective Hilbert--Schmidt distance, obtained
by instantiating the distance-independent theorem. -/
theorem clifford_t_is_universal_hs_via_projective {n : ℕ}
    (U : Square (2 ^ n))
    (hU : U ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ gates : List (Square (2 ^ n)),
      CircuitOver (CliffordTGate n) gates ∧
      hsDistance U (circuitMatrix gates) < ε := by
  simpa [hsProjectiveDistanceMeasure] using
    clifford_t_is_universal_projective
      (hsProjectiveDistanceMeasure (Nat.pow_pos (by decide : 0 < 2))) U hU hε

/-- **Universality of Clifford+T.**

Every finite-qubit unitary can be approximated arbitrarily accurately, up to
global phase, by a finite circuit over embedded CNOT, Hadamard, and T gates.
This backwards-compatible statement is the Hilbert--Schmidt specialization of
`clifford_t_is_universal_projective`. -/
theorem clifford_t_is_universal {n : ℕ}
    (U : Square (2 ^ n))
    (hU : U ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ gates : List (Square (2 ^ n)),
      CircuitOver (CliffordTGate n) gates ∧
      hsDistance U (circuitMatrix gates) < ε :=
  clifford_t_is_universal_hs_via_projective U hU hε

end Universal
end Clifford
end TwoControl
