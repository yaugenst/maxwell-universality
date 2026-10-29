import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.PiL2
import Maxwell.Green.Jet

/-! Actual principal coordinates on the plane perpendicular to a nonzero
three-dimensional propagation direction. -/

noncomputable section

namespace Maxwell.Green

open scoped InnerProductSpace

abbrev MomentumSpace := EuclideanSpace ℝ (Fin 3)
def transverseSpace (v : MomentumSpace) : Submodule ℝ MomentumSpace := (ℝ ∙ v)ᗮ

theorem transverseSpace_finrank (v : MomentumSpace) (hv : v ≠ 0) :
    Module.finrank ℝ (transverseSpace v) = 2 := by
  apply Submodule.finrank_add_finrank_orthogonal'
  simp [finrank_span_singleton hv]

def transverseForm (v : MomentumSpace) (B : MomentumSpace →L[ℝ] MomentumSpace →L[ℝ] ℝ) :
    transverseSpace v →L[ℝ] transverseSpace v →L[ℝ] ℝ :=
  B.bilinearComp (transverseSpace v).subtypeL (transverseSpace v).subtypeL

def transverseOperator (v : MomentumSpace)
    (B : MomentumSpace →L[ℝ] MomentumSpace →L[ℝ] ℝ) :
    transverseSpace v →L[ℝ] transverseSpace v :=
  (InnerProductSpace.toDual ℝ (transverseSpace v)).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (transverseForm v B)

theorem transverseOperator_inner (v : MomentumSpace)
    (B : MomentumSpace →L[ℝ] MomentumSpace →L[ℝ] ℝ) (x y : transverseSpace v) :
    ⟪transverseOperator v B x, y⟫_ℝ = B x y := by
  change ⟪(InnerProductSpace.toDual ℝ (transverseSpace v)).symm (transverseForm v B x), y⟫_ℝ = _
  rw [InnerProductSpace.toDual_symm_apply]
  rfl

theorem transverseOperator_symmetric (v : MomentumSpace)
    (B : MomentumSpace →L[ℝ] MomentumSpace →L[ℝ] ℝ)
    (hB : ∀ x y, B x y = B y x) : (transverseOperator v B).toLinearMap.IsSymmetric := by
  intro x y
  change ⟪transverseOperator v B x, y⟫_ℝ = ⟪x, transverseOperator v B y⟫_ℝ
  rw [transverseOperator_inner, real_inner_comm, transverseOperator_inner]
  exact hB _ _

/-- The transverse axes and positive principal Hessian coefficients are
constructed by the real spectral theorem, with no supplied diagonalizer. -/
theorem exists_transverse_principal_basis (v : MomentumSpace) (hv : v ≠ 0)
    (B : MomentumSpace →L[ℝ] MomentumSpace →L[ℝ] ℝ)
    (hB : ∀ x y, B x y = B y x)
    (hpos : ∀ x : MomentumSpace, x ≠ 0 → 0 < B x x) :
    ∃ (b : OrthonormalBasis (Fin 2) ℝ (transverseSpace v)) (q : Fin 2 → ℝ),
      (∀ i, 0 < q i) ∧
      (∀ i j, B (b i) (b j) = if i = j then q i else 0) := by
  let T := (transverseOperator v B).toLinearMap
  have hT : T.IsSymmetric := transverseOperator_symmetric v B hB
  let hn := transverseSpace_finrank v hv
  let b := hT.eigenvectorBasis hn
  let q := hT.eigenvalues hn
  have hdiag (i j : Fin 2) : B (b i) (b j) = if i = j then q i else 0 := by
    have hb := b.orthonormal
    rw [orthonormal_iff_ite] at hb
    rw [← transverseOperator_inner]
    change ⟪T (b i), b j⟫_ℝ = _
    rw [hT.apply_eigenvectorBasis hn, real_inner_smul_left, hb]
    split_ifs <;> simp_all [q]
  refine ⟨b, q, ?_, hdiag⟩
  intro i
  have hne : (b i : MomentumSpace) ≠ 0 := by
    intro h
    have hz : b i = 0 := Subtype.ext h
    exact b.toBasis.ne_zero i hz
  have hp := hpos (b i) hne
  simpa only [hdiag, ite_true] using hp

def propagationNormal (v : MomentumSpace) : MomentumSpace := ‖v‖⁻¹ • v

theorem propagationNormal_norm (v : MomentumSpace) (hv : v ≠ 0) :
    ‖propagationNormal v‖ = 1 := by
  simp [propagationNormal, norm_smul, norm_ne_zero_iff.mpr hv]

theorem propagationNormal_inner_transverse (v : MomentumSpace) (x : transverseSpace v) :
    ⟪propagationNormal v, (x : MomentumSpace)⟫_ℝ = 0 := by
  rw [propagationNormal, real_inner_smul_left,
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp x.property, mul_zero]

theorem supportGradient_normal (v : MomentumSpace) (hv : v ≠ 0) (χ : ℝ) :
    ⟪χ • v, propagationNormal v⟫_ℝ = χ * ‖v‖ := by
  simp only [propagationNormal, real_inner_smul_left, inner_smul_right,
    real_inner_self_eq_norm_sq]
  field_simp

theorem supportGradient_transverse (v : MomentumSpace) (χ : ℝ) (x : transverseSpace v) :
    ⟪χ • v, (x : MomentumSpace)⟫_ℝ = 0 := by
  rw [real_inner_smul_left, Submodule.mem_orthogonal_singleton_iff_inner_right.mp x.property, mul_zero]

theorem transverse_quadratic_diagonal
    (v : MomentumSpace) (B : MomentumSpace →L[ℝ] MomentumSpace →L[ℝ] ℝ)
    (b : OrthonormalBasis (Fin 2) ℝ (transverseSpace v)) (q : Fin 2 → ℝ)
    (hdiag : ∀ i j, B (b i) (b j) = if i = j then q i else 0)
    (s t : ℝ) :
    B (s • (b 0 : MomentumSpace) + t • (b 1 : MomentumSpace))
      (s • (b 0 : MomentumSpace) + t • (b 1 : MomentumSpace)) = q 0 * s ^ 2 + q 1 * t ^ 2 := by
  simp [map_add, map_smul, hdiag]
  ring

end Maxwell.Green
