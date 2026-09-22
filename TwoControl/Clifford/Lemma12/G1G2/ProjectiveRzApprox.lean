import TwoControl.Clifford.Lemma12.G1G2.Orthogonality
import TwoControl.Clifford.Universal.ProjectiveDistance
import Mathlib.Topology.Algebra.Group.SubmonoidClosure

namespace TwoControl
namespace Clifford
namespace Lemma12
namespace G1G2

open Set
open Matrix
open Universal

/-!
# Distance-independent approximation of `R_z`

This is the distance-independent form of the `G₁/G₂` density argument.  It
uses only the four laws in `ProjectiveDistanceMeasure`; in particular, no
formula for Hilbert--Schmidt distance occurs below.
-/

/-- Positive natural multiples of an irrational point are dense on a circle.

The strictly positive exponent lets the density proof produce ordinary
repetitions of an `{H,T}` word without introducing inverse gates. -/
theorem positive_nat_mod_dense {a θ p δ : ℝ} [Fact (0 < p)]
    (hirr : Irrational (θ / p)) (hδ : 0 < δ) :
    ∃ m : ℕ, 0 < m ∧ ∃ l : ℤ,
      |(m : ℝ) * θ - a - (l : ℝ) * p| < δ := by
  have hdenseZ : DenseRange (fun k : ℤ => k • (θ : AddCircle p)) :=
    AddCircle.denseRange_zsmul_coe_iff.mpr hirr
  have hdenseN : DenseRange (fun k : ℕ => k • (θ : AddCircle p)) :=
    denseRange_zsmul_iff_nsmul.mp hdenseZ
  obtain ⟨n, hn⟩ := hdenseN.exists_dist_lt ((a : AddCircle p) - (θ : AddCircle p)) hδ
  refine ⟨n + 1, Nat.zero_lt_succ n, ?_⟩
  have hdist : dist (a : AddCircle p) ((n + 1) • (θ : AddCircle p)) < δ := by
    calc
      dist (a : AddCircle p) ((n + 1) • (θ : AddCircle p)) =
          dist (((a : AddCircle p) - (θ : AddCircle p)) + (θ : AddCircle p))
            (n • (θ : AddCircle p) + (θ : AddCircle p)) := by simp [succ_nsmul]
      _ = dist ((a : AddCircle p) - (θ : AddCircle p)) (n • (θ : AddCircle p)) :=
        dist_add_right _ _ _
      _ < δ := hn
  rw [← AddCircle.coe_nsmul, nsmul_eq_mul] at hdist
  rw [dist_eq_norm, ← QuotientAddGroup.mk_sub, AddCircle.norm_eq] at hdist
  refine ⟨- round (p⁻¹ * (a - ((n + 1 : ℕ) : ℝ) * θ)), ?_⟩
  rw [Int.cast_neg, ← abs_neg]
  convert hdist using 1
  all_goals ring_nf

/-- The Pauli vector associated with a real axis is Hermitian. -/
theorem pauliVec_isHermitian (n : EuclideanSpace ℝ (Fin 3)) :
    (pauliVec n).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliVec, pauliX, pauliY, pauliZ]

/-- The evolution family from `ProjectiveDistanceMeasure` specializes to an
axis rotation after multiplying its parameter by `π`. -/
theorem hermitianEvolution_pauliVec (n : EuclideanSpace ℝ (Fin 3)) (t : ℝ) :
    hermitianEvolution (pauliVec n) t = axisRotation n (t * Real.pi) := by
  unfold hermitianEvolution axisRotation
  congr 2
  push_cast
  ring

/-- Natural powers preserve projective equivalence. -/
theorem globalPhaseEquivalent_pow {N : ℕ} {U V : Square N}
    (hUV : GlobalPhaseEquivalent U V) (m : ℕ) :
    GlobalPhaseEquivalent (U ^ m) (V ^ m) := by
  induction m with
  | zero => simp [GlobalPhaseEquivalent.refl]
  | succ m ih =>
      rw [pow_succ', pow_succ']
      exact GlobalPhaseEquivalent.mul hUV ih

/-- Irrational rotations have dense positive powers for every projective
distance measure.  This is the only place where continuity is used in the
one-qubit density proof. -/
theorem axisRotation_positive_powers_dense
    (d : ProjectiveDistanceMeasure 2)
    (n : EuclideanSpace ℝ (Fin 3)) (hn : ‖n‖ = 1)
    (θ α : ℝ) (hirr : Irrational (θ / (2 * Real.pi)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ m : ℕ, 0 < m ∧
      d (axisRotation n α) ((axisRotation n θ) ^ m) < ε := by
  obtain ⟨δ, hδ, hcontinuous⟩ :=
    d.continuity (pauliVec n) (pauliVec_isHermitian n) (α / Real.pi) ε hε
  have hirr' : Irrational ((θ / Real.pi) / 2) := by
    have hratio : (θ / Real.pi) / 2 = θ / (2 * Real.pi) := by
      field_simp [Real.pi_ne_zero]
    rw [hratio]
    exact hirr
  letI : Fact (0 < (2 : ℝ)) := ⟨by norm_num⟩
  obtain ⟨m, hm, l, hclose⟩ :=
    positive_nat_mod_dense (a := α / Real.pi) (θ := θ / Real.pi)
      (p := 2) hirr' hδ
  refine ⟨m, hm, ?_⟩
  have hclose' :
      |α / Real.pi - ((m : ℝ) * (θ / Real.pi) - (l : ℝ) * 2)| < δ := by
    rw [← abs_neg]
    convert hclose using 1
    all_goals ring_nf
  have happ := hcontinuous
    ((m : ℝ) * (θ / Real.pi) - (l : ℝ) * 2) hclose'
  have htarget :
      hermitianEvolution (pauliVec n) (α / Real.pi) = axisRotation n α := by
    rw [hermitianEvolution_pauliVec]
    congr 2
    field_simp [Real.pi_ne_zero]
  have hpower :
      hermitianEvolution (pauliVec n)
          ((m : ℝ) * (θ / Real.pi) - (l : ℝ) * 2) =
        (axisRotation n θ) ^ m := by
    rw [hermitianEvolution_pauliVec, axisRotation_nat_pow]
    have hangle :
        ((m : ℝ) * (θ / Real.pi) - (l : ℝ) * 2) * Real.pi =
          (m : ℝ) * θ + ((-l : ℤ) : ℝ) * (2 * Real.pi) := by
      push_cast
      field_simp [Real.pi_ne_zero]
      ring
    rw [hangle, axisRotation_add_int_mul_two_pi n hn]
  simpa [htarget, hpower] using happ

/-- A circuit word which realizes an irrational axis rotation up to global
phase has positive powers approaching every rotation about that axis. -/
theorem circuitWord_positive_powers_dense
    (d : ProjectiveDistanceMeasure 2)
    (n : EuclideanSpace ℝ (Fin 3)) (hn : ‖n‖ = 1)
    (C : HTCircuit) (z : ℂ) (hz : ‖z‖ = 1) (θ α : ℝ)
    (hC : HTCircuit.eval C = z • axisRotation n θ)
    (hirr : Irrational (θ / (2 * Real.pi)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ m : ℕ, 0 < m ∧
      d (axisRotation n α) (HTCircuit.eval (circuitPower C m)) < ε := by
  obtain ⟨m, hm, happrox⟩ :=
    axisRotation_positive_powers_dense d n hn θ α hirr hε
  refine ⟨m, hm, ?_⟩
  rw [circuitPower_eval]
  have hbase :
      GlobalPhaseEquivalent (HTCircuit.eval C) (axisRotation n θ) :=
    ⟨z, hz, hC⟩
  have hpowers :
      GlobalPhaseEquivalent ((axisRotation n θ) ^ m) ((HTCircuit.eval C) ^ m) :=
    GlobalPhaseEquivalent.symm (globalPhaseEquivalent_pow hbase m)
  rw [← d.eq_of_equivalent_right
    (axisRotation_mem_unitaryGroup n hn α)
    (Submonoid.pow_mem _ (axisRotation_mem_unitaryGroup n hn θ) m)
    (Submonoid.pow_mem _ (HTCircuit_eval_mem_unitaryGroup C) m)
    hpowers]
  exact happrox

/-- Distance-independent form of the paper's `R_z` approximation lemma. -/
theorem HT_rz_dense_projective
    (d : ProjectiveDistanceMeasure 2) (θ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : HTCircuit, d (rz θ) (HTCircuit.eval C) < ε := by
  obtain ⟨n₁, n₂, α₁, α₂, hn₁, hn₂, hg1, hg2, hirr₁, hirr₂, hortho⟩ :=
    g_axes_data
  obtain ⟨a, b, c, hEuler⟩ :=
    standardZ_axisRotation_orthogonal_euler n₁ n₂ hn₁ hn₂ hortho (-(θ / 2))
  have hε3 : 0 < ε / 3 := by positivity
  have hU1 : HTCircuit.eval g1Word = gPhase⁻¹ • axisRotation n₁ α₁ := by
    rw [g1Word_eval, hg1]
  have hU2 : HTCircuit.eval g2Word = gPhase⁻¹ • axisRotation n₂ α₂ := by
    rw [g2Word_eval, hg2]
  obtain ⟨m₁, _hm₁, h1⟩ := circuitWord_positive_powers_dense d n₁ hn₁
    g1Word gPhase⁻¹ gPhase_inv_norm α₁ a hU1 hirr₁ hε3
  obtain ⟨m₂, _hm₂, h2⟩ := circuitWord_positive_powers_dense d n₂ hn₂
    g2Word gPhase⁻¹ gPhase_inv_norm α₂ b hU2 hirr₂ hε3
  obtain ⟨m₃, _hm₃, h3⟩ := circuitWord_positive_powers_dense d n₁ hn₁
    g1Word gPhase⁻¹ gPhase_inv_norm α₁ c hU1 hirr₁ hε3
  let C₁ := circuitPower g1Word m₁
  let C₂ := circuitPower g2Word m₂
  let C₃ := circuitPower g1Word m₃
  refine ⟨C₁ ++ C₂ ++ C₃, ?_⟩
  rw [rz_eq_axisRotation_standardZ, hEuler, HTCircuit_eval_append,
    HTCircuit_eval_append]
  have hA := axisRotation_mem_unitaryGroup n₁ hn₁ a
  have hB := axisRotation_mem_unitaryGroup n₂ hn₂ b
  have hC := axisRotation_mem_unitaryGroup n₁ hn₁ c
  have hA' := HTCircuit_eval_mem_unitaryGroup C₁
  have hB' := HTCircuit_eval_mem_unitaryGroup C₂
  have hC' := HTCircuit_eval_mem_unitaryGroup C₃
  have hAB := Submonoid.mul_mem _ hA hB
  have hAB' := Submonoid.mul_mem _ hA' hB'
  have hfirst := d.subadditivity
    (axisRotation n₁ a) (axisRotation n₂ b)
    (HTCircuit.eval C₁) (HTCircuit.eval C₂) hA hB hA' hB'
  have hsecond := d.subadditivity
    (axisRotation n₁ a * axisRotation n₂ b) (axisRotation n₁ c)
    (HTCircuit.eval C₁ * HTCircuit.eval C₂) (HTCircuit.eval C₃)
    hAB hC hAB' hC'
  dsimp [C₁, C₂, C₃] at h1 h2 h3 ⊢
  linarith

end G1G2
end Lemma12
end Clifford
end TwoControl
