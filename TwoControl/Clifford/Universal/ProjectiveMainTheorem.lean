import TwoControl.Clifford.Universal.CliffordRz
import TwoControl.Clifford.Universal.ProjectiveRzApproximation

namespace TwoControl
namespace Clifford
namespace Universal

/-!
# Distance-independent universality of Clifford+T

This is the metric-independent proof path.  It depends only on the abstract
projective-distance interface and does not import a concrete distance formula.
-/

private theorem circuitMatrix_mem_unitaryGroup {N : ℕ}
    {allowed : Square N → Prop} {gates : List (Square N)}
    (hAllowedUnitary :
      ∀ {gate : Square N}, allowed gate → gate ∈ Matrix.unitaryGroup (Fin N) ℂ)
    (hGates : CircuitOver allowed gates) :
    circuitMatrix gates ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  induction gates with
  | nil => simp
  | cons gate gates ih =>
      have hgate := hAllowedUnitary (hGates gate (by simp))
      have htail := ih (by
        intro tailGate htailGate
        exact hGates tailGate (by simp [htailGate]))
      simpa [circuitMatrix] using Submonoid.mul_mem _ hgate htail

private theorem clifford_trz_gate_as_clifford_t_or_rz {n : ℕ}
    {gate : Square (2 ^ n)} (hgate : CliffordTRzGate n gate) :
    CliffordTGate n gate ∨ ∃ θ : ℝ, IsEmbeddedOneQubitGate n (rz θ) gate := by
  rcases hgate with hCnot | hH | hT | hRz
  · exact Or.inl (Or.inl hCnot)
  · exact Or.inl (Or.inr (Or.inl hH))
  · exact Or.inl (Or.inr (Or.inr hT))
  · exact Or.inr hRz

private theorem one_gate_replacement_projective {n : ℕ}
    (d : ProjectiveDistanceMeasure (2 ^ n))
    {gate : Square (2 ^ n)} (hgate : CliffordTRzGate n gate)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ replacement : List (Square (2 ^ n)),
      CircuitOver (CliffordTGate n) replacement ∧
      d gate (circuitMatrix replacement) < δ ∧
      circuitMatrix replacement ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ := by
  rcases clifford_trz_gate_as_clifford_t_or_rz hgate with hCliffordT | hRz
  · refine ⟨[gate], ?_, ?_, ?_⟩
    · intro candidate hcandidate
      have hcandidate_eq : candidate = gate := by simpa using hcandidate
      simpa [hcandidate_eq] using hCliffordT
    · have hunit := CliffordTGate.mem_unitaryGroup hCliffordT
      simpa using (show d gate gate < δ by rw [d.reflexivity gate hunit]; exact hδ)
    · simpa using CliffordTGate.mem_unitaryGroup hCliffordT
  · rcases hRz with ⟨θ, hEmbedded⟩
    rcases embedded_rz_approximation_by_clifford_t_projective
        d hδ hEmbedded with
      ⟨replacement, hReplacement, hDistance⟩
    refine ⟨replacement, hReplacement, hDistance, ?_⟩
    exact circuitMatrix_mem_unitaryGroup
      (allowed := CliffordTGate n)
      (fun hAllowed => CliffordTGate.mem_unitaryGroup hAllowed)
      hReplacement

private theorem clifford_rz_circuit_replacement_projective {n : ℕ}
    (d : ProjectiveDistanceMeasure (2 ^ n))
    {gates : List (Square (2 ^ n))}
    (hGates : CircuitOver (CliffordTRzGate n) gates)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ replacement : List (Square (2 ^ n)),
      CircuitOver (CliffordTGate n) replacement ∧
      d (circuitMatrix gates) (circuitMatrix replacement) ≤
        (gates.length : ℝ) * δ ∧
      circuitMatrix replacement ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ := by
  induction gates with
  | nil =>
      refine ⟨[], CircuitOver_nil _, ?_, by simp⟩
      have hone : (1 : Square (2 ^ n)) ∈
          Matrix.unitaryGroup (Fin (2 ^ n)) ℂ := Submonoid.one_mem _
      simp [d.reflexivity (1 : Square (2 ^ n)) hone]
  | cons gate tail ih =>
      have hgate : CliffordTRzGate n gate := hGates gate (by simp)
      have htail : CircuitOver (CliffordTRzGate n) tail := by
        intro tailGate htailGate
        exact hGates tailGate (by simp [htailGate])
      rcases one_gate_replacement_projective d hgate hδ with
        ⟨gateReplacement, hGateReplacement, hGateDistance, hGateUnitary⟩
      rcases ih htail with
        ⟨tailReplacement, hTailReplacement, hTailDistance, hTailUnitary⟩
      refine ⟨gateReplacement ++ tailReplacement,
        CircuitOver_append hGateReplacement hTailReplacement, ?_, ?_⟩
      · have hOriginalGateUnitary := CliffordTRzGate.mem_unitaryGroup hgate
        have hOriginalTailUnitary := circuitMatrix_mem_unitaryGroup
          (allowed := CliffordTRzGate n)
          (fun hAllowed => CliffordTRzGate.mem_unitaryGroup hAllowed) htail
        have hProduct := d.subadditivity gate (circuitMatrix tail)
          (circuitMatrix gateReplacement) (circuitMatrix tailReplacement)
          hOriginalGateUnitary hOriginalTailUnitary hGateUnitary hTailUnitary
        rw [circuitMatrix_append]
        change d (gate * circuitMatrix tail)
            (circuitMatrix gateReplacement * circuitMatrix tailReplacement) ≤
          ((tail.length + 1 : ℕ) : ℝ) * δ
        calc
          d (gate * circuitMatrix tail)
              (circuitMatrix gateReplacement * circuitMatrix tailReplacement) ≤
              d gate (circuitMatrix gateReplacement) +
                d (circuitMatrix tail) (circuitMatrix tailReplacement) := hProduct
          _ ≤ δ + (tail.length : ℝ) * δ :=
            add_le_add (le_of_lt hGateDistance) hTailDistance
          _ = ((tail.length + 1 : ℕ) : ℝ) * δ := by
            push_cast
            ring
      · rw [circuitMatrix_append]
        exact Submonoid.mul_mem _ hGateUnitary hTailUnitary

/-- Replace an exact Clifford+`R_z` synthesis by a Clifford+T circuit for an
arbitrary projective distance measure. -/
theorem clifford_rz_synthesis_approximates_by_clifford_t_projective {n : ℕ}
    (d : ProjectiveDistanceMeasure (2 ^ n))
    (U : Square (2 ^ n))
    (hU : U ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ)
    (hSynth : SynthesizesUpToGlobalPhase (CliffordTRzGate n) U)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ gates : List (Square (2 ^ n)),
      CircuitOver (CliffordTGate n) gates ∧
      d U (circuitMatrix gates) < ε := by
  rcases hSynth with ⟨rzGates, hRzGates, hPhase⟩
  let denom : ℝ := (rzGates.length : ℝ) + 1
  let δ : ℝ := ε / denom
  have hDenPos : 0 < denom := by dsimp [denom]; positivity
  have hδ : 0 < δ := div_pos hε hDenPos
  rcases clifford_rz_circuit_replacement_projective d hRzGates hδ with
    ⟨replacement, hReplacement, hDistance, hReplacementUnitary⟩
  refine ⟨replacement, hReplacement, ?_⟩
  have hOriginalUnitary := circuitMatrix_mem_unitaryGroup
    (allowed := CliffordTRzGate n)
    (fun hAllowed => CliffordTRzGate.mem_unitaryGroup hAllowed) hRzGates
  rw [d.eq_of_equivalent_left
    hU hOriginalUnitary hReplacementUnitary hPhase]
  refine lt_of_le_of_lt hDistance ?_
  have hLenLt : (rzGates.length : ℝ) < denom := by dsimp [denom]; linarith
  calc
    (rzGates.length : ℝ) * δ = (rzGates.length : ℝ) * ε / denom := by
      dsimp [δ]
      ring
    _ < denom * ε / denom := by
      exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_right hLenLt hε) hDenPos
    _ = ε := by field_simp [ne_of_gt hDenPos]

private theorem norm_eq_one_of_conj_mul_eq_one {z : ℂ} (hz : star z * z = 1) :
    ‖z‖ = 1 := by
  have hsq : ‖z‖ ^ 2 = 1 := by
    have hsq_complex : (((‖z‖ ^ 2 : ℝ) : ℂ)) = 1 := by
      calc
        (((‖z‖ ^ 2 : ℝ) : ℂ)) = star z * z := by
          rw [← Complex.normSq_eq_norm_sq]
          simpa using Complex.normSq_eq_conj_mul_self (z := z)
        _ = 1 := hz
    exact_mod_cast hsq_complex
  nlinarith [norm_nonneg z]

private theorem one_by_one_globalPhaseEquivalent_one
    (U : Square 1) (hU : U ∈ Matrix.unitaryGroup (Fin 1) ℂ) :
    GlobalPhaseEquivalent U (1 : Square 1) := by
  refine ⟨U 0 0, ?_, ?_⟩
  · apply norm_eq_one_of_conj_mul_eq_one
    have hUnitary : U * star U = (1 : Square 1) := Matrix.mem_unitaryGroup_iff.mp hU
    have hEntry := congrFun (congrFun hUnitary 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_one, mul_comm] using hEntry
  · ext i j
    fin_cases i
    fin_cases j
    simp

private theorem zero_qubit_clifford_t_is_universal_projective
    (d : ProjectiveDistanceMeasure 1)
    (U : Square 1) (hU : U ∈ Matrix.unitaryGroup (Fin 1) ℂ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ gates : List (Square 1),
      CircuitOver (CliffordTGate 0) gates ∧ d U (circuitMatrix gates) < ε := by
  refine ⟨[], CircuitOver_nil _, ?_⟩
  have hone : (1 : Square 1) ∈ Matrix.unitaryGroup (Fin 1) ℂ := Submonoid.one_mem _
  have hPhase := one_by_one_globalPhaseEquivalent_one U hU
  simpa using (show d U (1 : Square 1) < ε by
    rw [d.eq_zero_of_equivalent hU hone hPhase]
    exact hε)

/-- **Distance-independent universality of Clifford+T.**

For every projective distance satisfying reflexivity, global-phase
consistency, multiplicative subadditivity, and continuity along Hermitian
one-parameter evolutions, Clifford+T approximates every finite-qubit unitary
arbitrarily accurately. -/
theorem clifford_t_is_universal_projective {n : ℕ}
    (d : ProjectiveDistanceMeasure (2 ^ n))
    (U : Square (2 ^ n))
    (hU : U ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ gates : List (Square (2 ^ n)),
      CircuitOver (CliffordTGate n) gates ∧
      d U (circuitMatrix gates) < ε := by
  cases n with
  | zero => simpa using zero_qubit_clifford_t_is_universal_projective d U hU hε
  | succ m =>
      exact clifford_rz_synthesis_approximates_by_clifford_t_projective d U hU
        (clifford_rz_to_clifford_t_rz
          (clifford_rz_universal (Nat.succ_le_succ (Nat.zero_le m)) U hU)) hε

end Universal
end Clifford
end TwoControl
