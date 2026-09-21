import TwoControl.Clifford.Lemma12.G1G2.ProjectiveRzApprox

namespace TwoControl
namespace Clifford
namespace Universal

/-!
# Distance-independent embedded rotation approximation

This module lifts the one-qubit `G₁`/`G₂` density theorem through the concrete
wire-placement homomorphisms.  It deliberately does not import or mention a
particular distance formula.
-/

private theorem twoQubitCliffordTCircuitMatrix_onFirst
    (gates : List OneQubitHTPrimitive) :
    twoQubitCliffordTCircuitMatrix (gates.map TwoQubitCliffordTPrimitive.onFirst) =
      localOnFirst (oneQubitHTCircuitMatrix gates) := by
  induction gates with
  | nil =>
      simp [twoQubitCliffordTCircuitMatrix, oneQubitHTCircuitMatrix, localOnFirst,
        TwoControl.one_kron_one]
  | cons gate gates ih =>
      calc
        twoQubitCliffordTCircuitMatrix
            ((gate :: gates).map TwoQubitCliffordTPrimitive.onFirst)
            = localOnFirst (OneQubitHTPrimitive.eval gate) *
                twoQubitCliffordTCircuitMatrix
                  (gates.map TwoQubitCliffordTPrimitive.onFirst) := by
                simp [twoQubitCliffordTCircuitMatrix, TwoQubitCliffordTPrimitive.eval]
        _ = localOnFirst (OneQubitHTPrimitive.eval gate) *
              localOnFirst (oneQubitHTCircuitMatrix gates) := by rw [ih]
        _ = localOnFirst
              (OneQubitHTPrimitive.eval gate * oneQubitHTCircuitMatrix gates) := by
                rw [localOnFirst_mul_eq]
        _ = localOnFirst (oneQubitHTCircuitMatrix (gate :: gates)) := by rfl

private theorem twoQubitCliffordTCircuitMatrix_onSecond
    (gates : List OneQubitHTPrimitive) :
    twoQubitCliffordTCircuitMatrix (gates.map TwoQubitCliffordTPrimitive.onSecond) =
      localOnSecond (oneQubitHTCircuitMatrix gates) := by
  induction gates with
  | nil =>
      simp [twoQubitCliffordTCircuitMatrix, oneQubitHTCircuitMatrix, localOnSecond,
        TwoControl.one_kron_one]
  | cons gate gates ih =>
      calc
        twoQubitCliffordTCircuitMatrix
            ((gate :: gates).map TwoQubitCliffordTPrimitive.onSecond)
            = localOnSecond (OneQubitHTPrimitive.eval gate) *
                twoQubitCliffordTCircuitMatrix
                  (gates.map TwoQubitCliffordTPrimitive.onSecond) := by
                simp [twoQubitCliffordTCircuitMatrix, TwoQubitCliffordTPrimitive.eval]
        _ = localOnSecond (OneQubitHTPrimitive.eval gate) *
              localOnSecond (oneQubitHTCircuitMatrix gates) := by rw [ih]
        _ = localOnSecond
              (OneQubitHTPrimitive.eval gate * oneQubitHTCircuitMatrix gates) := by
                rw [localOnSecond_mul_eq]
        _ = localOnSecond (oneQubitHTCircuitMatrix (gate :: gates)) := by rfl

/-- Approximate an embedded `R_z` gate for an arbitrary projective distance.

The ambient distance is pulled back along the placement homomorphism, so the
theorem assumes no tensor- or embedding-invariance law. -/
theorem embedded_rz_approximation_by_clifford_t_projective {n : ℕ}
    (d : ProjectiveDistanceMeasure (2 ^ n))
    {R : Square (2 ^ n)} {θ ε : ℝ}
    (hε : 0 < ε)
    (hR : IsEmbeddedOneQubitGate n (rz θ) R) :
    ∃ gates : List (Square (2 ^ n)),
      CircuitOver (CliffordTGate n) gates ∧
      d R (circuitMatrix gates) < ε := by
  rcases hR with ⟨p, rfl⟩ | ⟨p, rfl⟩ | ⟨p, rfl⟩
  · obtain ⟨gatesHT, hApprox⟩ :=
      TwoControl.Clifford.Lemma12.G1G2.HT_rz_dense_projective
        (d.comap p.embedStarAlgHom) θ hε
    refine ⟨embedOneQubitHTCircuit p gatesHT,
      CircuitOver_embedOneQubitHTCircuit_cliffordT p gatesHT, ?_⟩
    rw [circuitMatrix_embedOneQubitHTCircuit]
    exact hApprox
  · obtain ⟨gatesHT, hApprox⟩ :=
      TwoControl.Clifford.Lemma12.G1G2.HT_rz_dense_projective
        (d.comap p.embedLocalOnFirstStarAlgHom) θ hε
    refine ⟨embedTwoQubitCliffordTCircuit p
        (gatesHT.map TwoQubitCliffordTPrimitive.onFirst),
      CircuitOver_embedTwoQubitCliffordTCircuit_cliffordT p
        (gatesHT.map TwoQubitCliffordTPrimitive.onFirst), ?_⟩
    rw [circuitMatrix_embedTwoQubitCliffordTCircuit,
      twoQubitCliffordTCircuitMatrix_onFirst]
    exact hApprox
  · obtain ⟨gatesHT, hApprox⟩ :=
      TwoControl.Clifford.Lemma12.G1G2.HT_rz_dense_projective
        (d.comap p.embedLocalOnSecondStarAlgHom) θ hε
    refine ⟨embedTwoQubitCliffordTCircuit p
        (gatesHT.map TwoQubitCliffordTPrimitive.onSecond),
      CircuitOver_embedTwoQubitCliffordTCircuit_cliffordT p
        (gatesHT.map TwoQubitCliffordTPrimitive.onSecond), ?_⟩
    rw [circuitMatrix_embedTwoQubitCliffordTCircuit,
      twoQubitCliffordTCircuitMatrix_onSecond]
    exact hApprox

end Universal
end Clifford
end TwoControl
