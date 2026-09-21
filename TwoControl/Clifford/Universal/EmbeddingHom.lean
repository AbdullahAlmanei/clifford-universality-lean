import TwoControl.Clifford.Universal.GateSets
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

open Matrix

namespace TwoControl
namespace Clifford
namespace Universal

/-!
# Algebraic gate embeddings

This file packages the local gate embeddings as continuous star algebra
homomorphisms.  In particular, it provides the algebraic interface needed to
transport matrix exponentials into an ambient multi-qubit space without
assuming anything about a distance measure.
-/

theorem reindexSquare_map_add {N M : ℕ} (e : Fin N ≃ Fin M) (U V : Square N) :
    reindexSquare e (U + V) = reindexSquare e U + reindexSquare e V := by
  ext i j
  rfl

theorem reindexSquare_map_smul {N M : ℕ} (e : Fin N ≃ Fin M) (c : ℂ) (U : Square N) :
    reindexSquare e (c • U) = c • reindexSquare e U := by
  simp [reindexSquare]

theorem castSquare_map_add {N M : ℕ} (h : N = M) (U V : Square N) :
    castSquare h (U + V) = castSquare h U + castSquare h V :=
  reindexSquare_map_add _ _ _

theorem castSquare_map_smul {N M : ℕ} (h : N = M) (c : ℂ) (U : Square N) :
    castSquare h (c • U) = c • castSquare h U :=
  reindexSquare_map_smul _ _ _

theorem castSquare_map_conjTranspose {N M : ℕ} (h : N = M) (U : Square N) :
    (castSquare h U)† = castSquare h U† := by
  simpa [castSquare] using
    reindexSquare_conjTranspose (Equiv.cast (congrArg Fin h)) U

namespace OneQubitPlacement

variable {n : ℕ} (p : OneQubitPlacement n)

theorem tensor_map_add (U V : Square 2) :
    p.tensor (U + V) = p.tensor U + p.tensor V := by
  simp only [tensor]
  rw [kron_add_left, KronHelpers.kron_add_right]

theorem tensor_map_smul (c : ℂ) (U : Square 2) :
    p.tensor (c • U) = c • p.tensor U := by
  simp only [tensor]
  rw [kron_smul_left, KronHelpers.kron_smul_right]

theorem tensor_map_conjTranspose (U : Square 2) :
    (p.tensor U)† = p.tensor U† := by
  unfold tensor
  rw [KronHelpers.conjTranspose_kron_reindex,
    KronHelpers.conjTranspose_kron_reindex]
  simp

theorem embed_map_add (U V : Square 2) :
    p.embed (U + V) = p.embed U + p.embed V := by
  simp only [embed]
  rw [p.tensor_map_add, castSquare_map_add, reindexSquare_map_add]

theorem embed_map_smul (c : ℂ) (U : Square 2) :
    p.embed (c • U) = c • p.embed U := by
  simp only [embed]
  rw [p.tensor_map_smul, castSquare_map_smul, reindexSquare_map_smul]

theorem embed_map_conjTranspose (U : Square 2) :
    (p.embed U)† = p.embed U† := by
  unfold embed
  rw [reindexSquare_conjTranspose, castSquare_map_conjTranspose,
    p.tensor_map_conjTranspose]

/-- A one-qubit placement as a complex-linear map. -/
noncomputable def embedLinearMap : Square 2 →ₗ[ℂ] Square (2 ^ n) where
  toFun := p.embed
  map_add' := p.embed_map_add
  map_smul' := p.embed_map_smul

/-- A one-qubit placement as a unital complex-algebra homomorphism. -/
noncomputable def embedAlgHom : Square 2 →ₐ[ℂ] Square (2 ^ n) :=
  AlgHom.ofLinearMap p.embedLinearMap p.embed_one p.embed_mul

@[simp] theorem embedAlgHom_apply (U : Square 2) :
    p.embedAlgHom U = p.embed U := rfl

/-- A one-qubit placement as a star-preserving complex-algebra homomorphism. -/
noncomputable def embedStarAlgHom : Square 2 →⋆ₐ[ℂ] Square (2 ^ n) where
  __ := p.embedAlgHom
  map_star' U := by
    change p.embed (star U) = star (p.embed U)
    rw [Matrix.star_eq_conjTranspose, Matrix.star_eq_conjTranspose,
      p.embed_map_conjTranspose]

@[simp] theorem embedStarAlgHom_apply (U : Square 2) :
    p.embedStarAlgHom U = p.embed U := rfl

theorem continuous_embed : Continuous p.embed := by
  change Continuous p.embedLinearMap
  exact p.embedLinearMap.continuous_of_finiteDimensional

end OneQubitPlacement

namespace TwoQubitPlacement

variable {n : ℕ} (p : TwoQubitPlacement n)

theorem tensor_map_add (U V : Square 4) :
    p.tensor (U + V) = p.tensor U + p.tensor V := by
  simp only [tensor]
  rw [kron_add_left, KronHelpers.kron_add_right]

theorem tensor_map_smul (c : ℂ) (U : Square 4) :
    p.tensor (c • U) = c • p.tensor U := by
  simp only [tensor]
  rw [kron_smul_left, KronHelpers.kron_smul_right]

theorem tensor_map_conjTranspose (U : Square 4) :
    (p.tensor U)† = p.tensor U† := by
  unfold tensor
  rw [KronHelpers.conjTranspose_kron_reindex,
    KronHelpers.conjTranspose_kron_reindex]
  simp

theorem embed_map_add (U V : Square 4) :
    p.embed (U + V) = p.embed U + p.embed V := by
  simp only [embed]
  rw [p.tensor_map_add, castSquare_map_add, reindexSquare_map_add]

theorem embed_map_smul (c : ℂ) (U : Square 4) :
    p.embed (c • U) = c • p.embed U := by
  simp only [embed]
  rw [p.tensor_map_smul, castSquare_map_smul, reindexSquare_map_smul]

theorem embed_map_conjTranspose (U : Square 4) :
    (p.embed U)† = p.embed U† := by
  unfold embed
  rw [reindexSquare_conjTranspose, castSquare_map_conjTranspose,
    p.tensor_map_conjTranspose]

/-- A two-qubit placement as a complex-linear map. -/
noncomputable def embedLinearMap : Square 4 →ₗ[ℂ] Square (2 ^ n) where
  toFun := p.embed
  map_add' := p.embed_map_add
  map_smul' := p.embed_map_smul

/-- A two-qubit placement as a unital complex-algebra homomorphism. -/
noncomputable def embedAlgHom : Square 4 →ₐ[ℂ] Square (2 ^ n) :=
  AlgHom.ofLinearMap p.embedLinearMap p.embed_one p.embed_mul

@[simp] theorem embedAlgHom_apply (U : Square 4) :
    p.embedAlgHom U = p.embed U := rfl

/-- A two-qubit placement as a star-preserving complex-algebra homomorphism. -/
noncomputable def embedStarAlgHom : Square 4 →⋆ₐ[ℂ] Square (2 ^ n) where
  __ := p.embedAlgHom
  map_star' U := by
    change p.embed (star U) = star (p.embed U)
    rw [Matrix.star_eq_conjTranspose, Matrix.star_eq_conjTranspose,
      p.embed_map_conjTranspose]

@[simp] theorem embedStarAlgHom_apply (U : Square 4) :
    p.embedStarAlgHom U = p.embed U := rfl

theorem continuous_embed : Continuous p.embed := by
  change Continuous p.embedLinearMap
  exact p.embedLinearMap.continuous_of_finiteDimensional

end TwoQubitPlacement

/-! ### Local one-qubit gates inside a two-qubit block -/

theorem localOnFirst_add (U V : Square 2) :
    localOnFirst (U + V) = localOnFirst U + localOnFirst V := by
  unfold localOnFirst
  rw [kron_add_left]

theorem localOnFirst_smul (c : ℂ) (U : Square 2) :
    localOnFirst (c • U) = c • localOnFirst U := by
  unfold localOnFirst
  rw [kron_smul_left]

theorem localOnFirst_one :
    localOnFirst (1 : Square 2) = (1 : Square 4) := by
  exact TwoControl.one_kron_one 2 2

theorem localOnFirst_mul_eq (U V : Square 2) :
    localOnFirst (U * V) = localOnFirst U * localOnFirst V := by
  unfold localOnFirst
  simpa using
    (KronHelpers.kron_mul_reindex (A := U) (B := V)
      (C := (1 : Square 2)) (D := (1 : Square 2)))

theorem localOnFirst_conjTranspose (U : Square 2) :
    (localOnFirst U)† = localOnFirst U† := by
  unfold localOnFirst
  simpa using
    KronHelpers.conjTranspose_kron_reindex (A := U) (B := (1 : Square 2))

noncomputable def localOnFirstLinearMap : Square 2 →ₗ[ℂ] Square 4 where
  toFun := localOnFirst
  map_add' := localOnFirst_add
  map_smul' := localOnFirst_smul

noncomputable def localOnFirstAlgHom : Square 2 →ₐ[ℂ] Square 4 :=
  AlgHom.ofLinearMap localOnFirstLinearMap localOnFirst_one localOnFirst_mul_eq

/-- `U ↦ U ⊗ I` as a star-preserving complex-algebra homomorphism. -/
noncomputable def localOnFirstStarAlgHom : Square 2 →⋆ₐ[ℂ] Square 4 where
  __ := localOnFirstAlgHom
  map_star' U := by
    change localOnFirst (star U) = star (localOnFirst U)
    rw [Matrix.star_eq_conjTranspose, Matrix.star_eq_conjTranspose,
      localOnFirst_conjTranspose]

@[simp] theorem localOnFirstStarAlgHom_apply (U : Square 2) :
    localOnFirstStarAlgHom U = localOnFirst U := rfl

theorem localOnSecond_add (U V : Square 2) :
    localOnSecond (U + V) = localOnSecond U + localOnSecond V := by
  unfold localOnSecond
  rw [KronHelpers.kron_add_right]

theorem localOnSecond_smul (c : ℂ) (U : Square 2) :
    localOnSecond (c • U) = c • localOnSecond U := by
  unfold localOnSecond
  rw [KronHelpers.kron_smul_right]

theorem localOnSecond_one :
    localOnSecond (1 : Square 2) = (1 : Square 4) := by
  exact TwoControl.one_kron_one 2 2

theorem localOnSecond_mul_eq (U V : Square 2) :
    localOnSecond (U * V) = localOnSecond U * localOnSecond V := by
  unfold localOnSecond
  simpa using
    (KronHelpers.kron_mul_reindex (A := (1 : Square 2)) (B := (1 : Square 2))
      (C := U) (D := V))

theorem localOnSecond_conjTranspose (U : Square 2) :
    (localOnSecond U)† = localOnSecond U† := by
  unfold localOnSecond
  simpa using
    KronHelpers.conjTranspose_kron_reindex (A := (1 : Square 2)) (B := U)

noncomputable def localOnSecondLinearMap : Square 2 →ₗ[ℂ] Square 4 where
  toFun := localOnSecond
  map_add' := localOnSecond_add
  map_smul' := localOnSecond_smul

noncomputable def localOnSecondAlgHom : Square 2 →ₐ[ℂ] Square 4 :=
  AlgHom.ofLinearMap localOnSecondLinearMap localOnSecond_one localOnSecond_mul_eq

/-- `U ↦ I ⊗ U` as a star-preserving complex-algebra homomorphism. -/
noncomputable def localOnSecondStarAlgHom : Square 2 →⋆ₐ[ℂ] Square 4 where
  __ := localOnSecondAlgHom
  map_star' U := by
    change localOnSecond (star U) = star (localOnSecond U)
    rw [Matrix.star_eq_conjTranspose, Matrix.star_eq_conjTranspose,
      localOnSecond_conjTranspose]

@[simp] theorem localOnSecondStarAlgHom_apply (U : Square 2) :
    localOnSecondStarAlgHom U = localOnSecond U := rfl

namespace TwoQubitPlacement

variable {n : ℕ} (p : TwoQubitPlacement n)

/-- A one-qubit gate on the first local wire, followed by a two-qubit placement. -/
noncomputable def embedLocalOnFirstStarAlgHom :
    Square 2 →⋆ₐ[ℂ] Square (2 ^ n) :=
  p.embedStarAlgHom.comp localOnFirstStarAlgHom

@[simp] theorem embedLocalOnFirstStarAlgHom_apply (U : Square 2) :
    p.embedLocalOnFirstStarAlgHom U = p.embed (localOnFirst U) := rfl

/-- A one-qubit gate on the second local wire, followed by a two-qubit placement. -/
noncomputable def embedLocalOnSecondStarAlgHom :
    Square 2 →⋆ₐ[ℂ] Square (2 ^ n) :=
  p.embedStarAlgHom.comp localOnSecondStarAlgHom

@[simp] theorem embedLocalOnSecondStarAlgHom_apply (U : Square 2) :
    p.embedLocalOnSecondStarAlgHom U = p.embed (localOnSecond U) := rfl

end TwoQubitPlacement

/-! ### Matrix exponentials -/

open scoped Matrix.Norms.Operator in
theorem StarAlgHom.map_matrix_exp {a b : ℕ}
    (f : Square a →⋆ₐ[ℂ] Square b) (U : Square a) :
    f (NormedSpace.exp U) = NormedSpace.exp (f U) := by
  have hf : Continuous f :=
    f.toAlgHom.toLinearMap.continuous_of_finiteDimensional
  exact NormedSpace.map_exp (𝔸 := Square a) (𝔹 := Square b)
    (F := Square a →+* Square b) f.toAlgHom.toRingHom hf U

theorem OneQubitPlacement.embed_exp {n : ℕ} (p : OneQubitPlacement n)
    (U : Square 2) :
    p.embed (NormedSpace.exp U) = NormedSpace.exp (p.embed U) := by
  simpa using StarAlgHom.map_matrix_exp p.embedStarAlgHom U

theorem TwoQubitPlacement.embed_exp {n : ℕ} (p : TwoQubitPlacement n)
    (U : Square 4) :
    p.embed (NormedSpace.exp U) = NormedSpace.exp (p.embed U) := by
  simpa using StarAlgHom.map_matrix_exp p.embedStarAlgHom U

theorem TwoQubitPlacement.embed_localOnFirst_exp {n : ℕ}
    (p : TwoQubitPlacement n) (U : Square 2) :
    p.embed (localOnFirst (NormedSpace.exp U)) =
      NormedSpace.exp (p.embed (localOnFirst U)) := by
  simpa using StarAlgHom.map_matrix_exp p.embedLocalOnFirstStarAlgHom U

theorem TwoQubitPlacement.embed_localOnSecond_exp {n : ℕ}
    (p : TwoQubitPlacement n) (U : Square 2) :
    p.embed (localOnSecond (NormedSpace.exp U)) =
      NormedSpace.exp (p.embed (localOnSecond U)) := by
  simpa using StarAlgHom.map_matrix_exp p.embedLocalOnSecondStarAlgHom U

end Universal
end Clifford
end TwoControl
