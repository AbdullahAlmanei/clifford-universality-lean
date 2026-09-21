import TwoControl.Clifford.Universal.EmbeddingHom

namespace TwoControl
namespace Clifford
namespace Universal

/-!
# Projective distance measures

The universality argument only needs four properties of a distance on unitary
matrices.  Keeping the distance dimension-specific is important: an
`n`-qubit universality proof invokes continuity only after every local gate has
been embedded into the ambient `2 ^ n` dimensional space.
-/

/-- The one-parameter unitary family `exp(i t pi A)` used by the continuity
property of a projective distance measure. -/
noncomputable def hermitianEvolution {N : ℕ} (A : Square N) (t : ℝ) : Square N :=
  NormedSpace.exp ((Complex.I * (t * Real.pi) : ℂ) • A)

/-- A projective distance measure on `N × N` unitary matrices.

The fields are Definition 3.3 of *Distance-Independent Universality of
Clifford+T*.  The function is defined on all square matrices to interoperate
with the existing circuit representation; the algebraic laws are required on
unitaries, which is its intended domain. -/
structure ProjectiveDistanceMeasure (N : ℕ) where
  distance : Square N → Square N → ℝ
  nonnegative : ∀ U V, 0 ≤ distance U V
  reflexivity : ∀ U,
    U ∈ Matrix.unitaryGroup (Fin N) ℂ → distance U U = 0
  consistency : ∀ U₁ U₂ V₁ V₂,
    U₁ ∈ Matrix.unitaryGroup (Fin N) ℂ →
    U₂ ∈ Matrix.unitaryGroup (Fin N) ℂ →
    V₁ ∈ Matrix.unitaryGroup (Fin N) ℂ →
    V₂ ∈ Matrix.unitaryGroup (Fin N) ℂ →
    GlobalPhaseEquivalent U₁ U₂ →
    GlobalPhaseEquivalent V₁ V₂ →
    distance U₁ V₁ = distance U₂ V₂
  subadditivity : ∀ U₁ U₂ V₁ V₂,
    U₁ ∈ Matrix.unitaryGroup (Fin N) ℂ →
    U₂ ∈ Matrix.unitaryGroup (Fin N) ℂ →
    V₁ ∈ Matrix.unitaryGroup (Fin N) ℂ →
    V₂ ∈ Matrix.unitaryGroup (Fin N) ℂ →
    distance (U₁ * U₂) (V₁ * V₂) ≤
      distance U₁ V₁ + distance U₂ V₂
  continuity : ∀ A, A.IsHermitian → ∀ t₀ ε, 0 < ε →
    ∃ δ, 0 < δ ∧ ∀ t, |t₀ - t| < δ →
      distance (hermitianEvolution A t₀) (hermitianEvolution A t) < ε

namespace ProjectiveDistanceMeasure

instance {N : ℕ} : CoeFun (ProjectiveDistanceMeasure N)
    (fun _ ↦ Square N → Square N → ℝ) :=
  ⟨ProjectiveDistanceMeasure.distance⟩

theorem eq_zero_of_equivalent {N : ℕ} (d : ProjectiveDistanceMeasure N)
    {U V : Square N}
    (hU : U ∈ Matrix.unitaryGroup (Fin N) ℂ)
    (hV : V ∈ Matrix.unitaryGroup (Fin N) ℂ)
    (hUV : GlobalPhaseEquivalent U V) :
    d U V = 0 := by
  calc
    d U V = d V V :=
      d.consistency U V V V hU hV hV hV hUV (GlobalPhaseEquivalent.refl V)
    _ = 0 := d.reflexivity V hV

theorem eq_of_equivalent_left {N : ℕ} (d : ProjectiveDistanceMeasure N)
    {U V W : Square N}
    (hU : U ∈ Matrix.unitaryGroup (Fin N) ℂ)
    (hV : V ∈ Matrix.unitaryGroup (Fin N) ℂ)
    (hW : W ∈ Matrix.unitaryGroup (Fin N) ℂ)
    (hUV : GlobalPhaseEquivalent U V) :
    d U W = d V W :=
  d.consistency U V W W hU hV hW hW hUV (GlobalPhaseEquivalent.refl W)

theorem eq_of_equivalent_right {N : ℕ} (d : ProjectiveDistanceMeasure N)
    {U V W : Square N}
    (hU : U ∈ Matrix.unitaryGroup (Fin N) ℂ)
    (hV : V ∈ Matrix.unitaryGroup (Fin N) ℂ)
    (hW : W ∈ Matrix.unitaryGroup (Fin N) ℂ)
    (hVW : GlobalPhaseEquivalent V W) :
    d U V = d U W :=
  d.consistency U U V W hU hU hV hW (GlobalPhaseEquivalent.refl U) hVW

private theorem StarAlgHom.map_mem_unitaryGroup {M N : ℕ}
    (f : Square M →⋆ₐ[ℂ] Square N) {U : Square M}
    (hU : U ∈ Matrix.unitaryGroup (Fin M) ℂ) :
    f U ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff'] at hU ⊢
  calc
    star (f U) * f U = f (star U) * f U := by rw [map_star]
    _ = f (star U * U) := by rw [map_mul]
    _ = 1 := by rw [hU, map_one]

private theorem StarAlgHom.map_globalPhaseEquivalent {M N : ℕ}
    (f : Square M →⋆ₐ[ℂ] Square N) {U V : Square M}
    (hUV : GlobalPhaseEquivalent U V) :
    GlobalPhaseEquivalent (f U) (f V) := by
  rcases hUV with ⟨z, hz, hUV⟩
  refine ⟨z, hz, ?_⟩
  rw [hUV, map_smul]

/-- Pull a projective distance back along a star-preserving algebra
homomorphism.  This is how the one-qubit density theorem is applied directly
to an arbitrary ambient `n`-qubit distance, without assuming that the distance
is invariant under tensor padding. -/
noncomputable def comap {M N : ℕ} (d : ProjectiveDistanceMeasure N)
    (f : Square M →⋆ₐ[ℂ] Square N) : ProjectiveDistanceMeasure M where
  distance U V := d (f U) (f V)
  nonnegative U V := d.nonnegative (f U) (f V)
  reflexivity U hU := d.reflexivity (f U) (StarAlgHom.map_mem_unitaryGroup f hU)
  consistency U₁ U₂ V₁ V₂ hU₁ hU₂ hV₁ hV₂ hU hV :=
    d.consistency (f U₁) (f U₂) (f V₁) (f V₂)
      (StarAlgHom.map_mem_unitaryGroup f hU₁)
      (StarAlgHom.map_mem_unitaryGroup f hU₂)
      (StarAlgHom.map_mem_unitaryGroup f hV₁)
      (StarAlgHom.map_mem_unitaryGroup f hV₂)
      (StarAlgHom.map_globalPhaseEquivalent f hU)
      (StarAlgHom.map_globalPhaseEquivalent f hV)
  subadditivity U₁ U₂ V₁ V₂ hU₁ hU₂ hV₁ hV₂ := by
    simpa using d.subadditivity (f U₁) (f U₂) (f V₁) (f V₂)
      (StarAlgHom.map_mem_unitaryGroup f hU₁)
      (StarAlgHom.map_mem_unitaryGroup f hU₂)
      (StarAlgHom.map_mem_unitaryGroup f hV₁)
      (StarAlgHom.map_mem_unitaryGroup f hV₂)
  continuity A hA t₀ ε hε := by
    have hfA : (f A).IsHermitian := by
      change star (f A) = f A
      rw [← map_star]
      have hAstar : star A = A := by
        simpa [Matrix.star_eq_conjTranspose] using hA
      rw [hAstar]
    obtain ⟨δ, hδ, hcont⟩ := d.continuity (f A) hfA t₀ ε hε
    refine ⟨δ, hδ, fun t ht ↦ ?_⟩
    have hevolution (s : ℝ) :
        f (hermitianEvolution A s) = hermitianEvolution (f A) s := by
      unfold hermitianEvolution
      rw [StarAlgHom.map_matrix_exp, map_smul]
    simpa [hevolution] using hcont t ht

end ProjectiveDistanceMeasure

theorem GlobalPhaseEquivalent.symm {N : ℕ} {U V : Square N}
    (hUV : GlobalPhaseEquivalent U V) : GlobalPhaseEquivalent V U := by
  rcases hUV with ⟨z, hz, rfl⟩
  have hz0 : z ≠ 0 := by
    intro hz0
    simp [hz0] at hz
  refine ⟨z⁻¹, by simp [hz], ?_⟩
  rw [smul_smul, inv_mul_cancel₀ hz0, one_smul]

end Universal
end Clifford
end TwoControl
