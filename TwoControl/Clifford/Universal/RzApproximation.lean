import TwoControl.Clifford.Universal.Distance
import TwoControl.Clifford.Universal.ProjectiveRzApproximation

namespace TwoControl
namespace Clifford
namespace Universal

/-!
# Hilbert--Schmidt specialization of embedded rotation approximation

The distance-independent proof is in `ProjectiveRzApproximation`.  This module
retains the original public Hilbert--Schmidt theorem as a derived corollary.
-/

/-- Embedded `R_z` approximation in projective Hilbert--Schmidt distance. -/
theorem embedded_rz_approximation_by_clifford_t {n : ℕ}
    {R : Square (2 ^ n)} {θ ε : ℝ}
    (hε : 0 < ε)
    (hR : IsEmbeddedOneQubitGate n (rz θ) R) :
    ∃ gates : List (Square (2 ^ n)),
      CircuitOver (CliffordTGate n) gates ∧
      hsDistance R (circuitMatrix gates) < ε := by
  simpa [hsProjectiveDistanceMeasure] using
    embedded_rz_approximation_by_clifford_t_projective
      (hsProjectiveDistanceMeasure (Nat.pow_pos (by decide : 0 < 2))) hε hR

end Universal
end Clifford
end TwoControl
