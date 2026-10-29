import Maxwell.Spectral.BlochResolvent
import Maxwell.Defect.FiniteCompression
import Maxwell.Defect.ConcreteFiniteStencil
import Maxwell.Defect.TorusChart
import Maxwell.Defect.PhysicalCompression

/-! The same actual finitely supported source determines both the lattice
compression and its Bloch integral. Translations are by full conventional
cells; the minus sign matches the positive Fourier phase of the saddle proof. -/
namespace Maxwell.Green.PhysicalCompression

open MeasureTheory Maxwell.Spectral Maxwell.Spectral.Lattice Maxwell.Spectral.Bloch
open Maxwell.Spectral.BlochResolvent
open scoped ENNReal

noncomputable section
variable {ι : Type*} [Fintype ι]
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

/-- The actual finite lattice field, with arbitrary complex coefficients. -/
def finiteField (edges : ι → Edge) (a : ι → ℂ) : Field :=
  ∑ i, lp.single 2 (edges i) (a i)

/-- Its finite Bloch polynomial, including all within-source cell phases. -/
def profile (edges : ι → Edge) (a : ι → ℂ) (t : Torus) (r : Edge20) : ℂ :=
  ∑ i, if r = (edgeCellEquiv (edges i)).1 then
    a i * UnitAddTorus.mFourier (-(edgeCellEquiv (edges i)).2) t else 0

theorem transform_finiteField_ae (edges : ι → Edge) (a : ι → ℂ) (r : Edge20) :
    transform (finiteField edges a) r =ᵐ[volume] fun t => profile edges a t r := by
  have hs : transform (finiteField edges a) r =
      ∑ i, transform (lp.single 2 (edges i) (a i)) r := by
    simp [finiteField]
  rw [hs]
  filter_upwards [Lp.coeFn_finsetSum Finset.univ
    (fun i => transform (lp.single 2 (edges i) (a i)) r),
    Filter.eventually_all.mpr (fun i => transform_single_component_ae (edges i) (a i) r)]
    with t ht hi
  rw [ht]
  simpa only [Finset.sum_apply, profile] using
    (Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ => hi i))

/-- A physical shift by minus twenty times an integer cell vector. -/
def translateEdge (n : Site) (e : Edge) : Edge := (e.1, e.2 - 20 • n)

theorem edgeCellEquiv_translate (n : Site) (e : Edge) :
    edgeCellEquiv (translateEdge n e) =
      ((edgeCellEquiv e).1, (edgeCellEquiv e).2 - n) := by
  obtain ⟨⟨r, k⟩, rfl⟩ := edgeCellEquiv.symm.surjective e
  apply edgeCellEquiv.symm.injective
  simp only [Equiv.symm_apply_apply, Equiv.apply_symm_apply]
  rw [edgeCellEquiv_symm_apply, edgeCellEquiv_symm_apply]
  apply Prod.ext
  · rfl
  · funext j
    simp only [translateEdge, Pi.sub_apply, Pi.smul_apply]
    ring

theorem translateEdge_injective (n : Site) : Function.Injective (translateEdge n) := by
  intro e f h
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  exact Prod.ext h₁ (sub_left_injective h₂)

/-- Translation contributes exactly the common Fourier character. -/
theorem profile_translate (edges : ι → Edge) (a : ι → ℂ) (n : Site)
    (t : Torus) (r : Edge20) :
    profile (translateEdge n ∘ edges) a t r =
      UnitAddTorus.mFourier n t * profile edges a t r := by
  unfold profile
  simp only [Function.comp_apply, edgeCellEquiv_translate]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs
  · rw [neg_sub, sub_eq_add_neg, UnitAddTorus.mFourier_add]
    ring
  · simp

/-- The actual compressed scalar coupling, before any spectral estimates. -/
def scalarCoupling (edges : ι → Edge) (a : ι → ℂ)
    (T : Field →L[ℂ] Field) (n : Site) : ℂ :=
  inner ℂ (finiteField edges a) (T (finiteField (translateEdge n ∘ edges) a))

def scalarAmplitude (edges : ι → Edge) (a : ι → ℂ)
    (m : Edge20 → ℝ) (z : ℝ) (t : Torus) : ℂ :=
  ∑ i, star (profile edges a t i) *
    (Ring.inverse (torusElectric m t - (z : ℂ) • 1)).mulVec (profile edges a t) i

/-- Exact Fourier formula for the same source and the actual infinite inverse.
There is no independent Green function or compressed-inverse premise. -/
theorem scalarCoupling_integral (edges : ι → Edge) (a : ι → ℂ)
    (m : Edge20 → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hm : ∀ e, |periodicCoefficient m e| ≤ K) (z : ℝ)
    (hz : ∀ t : Torus, z ∉ spectrum ℝ (torusElectric m t)) (n : Site) :
    scalarCoupling edges a
      (Ring.inverse (electricOperator (periodicCoefficient m) K hK hm - (z : ℂ) • 1)) n =
      ∫ t : Torus, UnitAddTorus.mFourier n t * scalarAmplitude edges a m z t := by
  unfold scalarCoupling
  rw [electric_inverse_inner_integral m K hK hm z hz]
  apply integral_congr_ae
  filter_upwards [Filter.eventually_all.mpr (fun i => transform_finiteField_ae edges a i),
    Filter.eventually_all.mpr (fun i => transform_finiteField_ae (translateEdge n ∘ edges) a i)]
    with t ht hu
  simp only [ht, hu, profile_translate, scalarAmplitude, Matrix.mulVec, dotProduct,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

section Compression
variable [DecidableEq ι]

def translatedEmbedding (edges : ι ↪ Edge) (n : Site) : ι ↪ Edge :=
  ⟨translateEdge n ∘ edges, (translateEdge_injective n).comp edges.injective⟩

/-- The genuine off-diagonal coordinate block of the lattice operator. -/
def offdiagonalCompression (edges : ι ↪ Edge) (T : Field →L[ℂ] Field) (n : Site) :
    EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι :=
  (Maxwell.Target.sequenceRestriction edges).comp
    (T.comp (Maxwell.Target.sequenceExtension (translatedEmbedding edges n)).toContinuousLinearMap)

theorem finiteField_extension (edges : ι ↪ Edge) (a : EuclideanSpace ℂ ι) :
    finiteField edges a = Maxwell.Target.sequenceExtension edges a := rfl

theorem offdiagonalCompression_inner (edges : ι ↪ Edge) (T : Field →L[ℂ] Field)
    (n : Site) (a : EuclideanSpace ℂ ι) :
    inner ℂ a (offdiagonalCompression edges T n a) = scalarCoupling edges a T n := by
  change inner ℂ a ((Maxwell.Target.sequenceExtension edges).toContinuousLinearMap.adjoint
    (T (Maxwell.Target.sequenceExtension (translatedEmbedding edges n) a))) = _
  rw [ContinuousLinearMap.adjoint_inner_right]
  rfl

theorem offdiagonalCompression_norm_le (edges : ι ↪ Edge) (T : Field →L[ℂ] Field)
    (n : Site) : ‖offdiagonalCompression edges T n‖ ≤ ‖T‖ := by
  have hQ := Maxwell.Target.sequenceExtension_norm_le (translatedEmbedding edges n)
  have hR := Maxwell.Target.sequenceRestriction_norm_le edges
  calc
    _ ≤ ‖Maxwell.Target.sequenceRestriction edges‖ *
      (‖T‖ * ‖(Maxwell.Target.sequenceExtension (translatedEmbedding edges n)).toContinuousLinearMap‖) :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1 * (‖T‖ * 1) := by gcongr
    _ = ‖T‖ := by ring

end Compression

/-- Both sides use the actual same square-root-weighted source injection. -/
def weightedBlock {N : ℕ} (edges : Fin N ↪ Edge) (W : Fin N → ℚ)
    (T : Field →L[ℂ] Field) (n : Site) :
    EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N) :=
  (Maxwell.Defect.defectInjection edges W).adjoint.comp
    (T.comp (Maxwell.Defect.defectInjection (translatedEmbedding edges n) W))

theorem weightedBlock_inner {N : ℕ} (edges : Fin N ↪ Edge) (W : Fin N → ℚ)
    (T : Field →L[ℂ] Field) (n : Site) (u : EuclideanSpace ℂ (Fin N)) :
    inner ℂ u (weightedBlock edges W T n u) =
      scalarCoupling edges (Maxwell.Defect.complexSqrtWeightOperator W u) T n := by
  change inner ℂ u ((Maxwell.Defect.defectInjection edges W).adjoint
    (T (Maxwell.Defect.defectInjection (translatedEmbedding edges n) W u))) = _
  rw [ContinuousLinearMap.adjoint_inner_right]
  rfl

theorem weightedBlock_integral {N : ℕ} (edges : Fin N ↪ Edge) (W : Fin N → ℚ)
    (u : EuclideanSpace ℂ (Fin N)) (m : Edge20 → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hm : ∀ e, |periodicCoefficient m e| ≤ K) (z : ℝ)
    (hz : ∀ t : Torus, z ∉ spectrum ℝ (torusElectric m t)) (n : Site) :
    inner ℂ u (weightedBlock edges W
      (Ring.inverse (electricOperator (periodicCoefficient m) K hK hm - (z : ℂ) • 1)) n u) =
      ∫ t : Torus, UnitAddTorus.mFourier n t * scalarAmplitude edges
        (Maxwell.Defect.complexSqrtWeightOperator W u) m z t := by
  rw [weightedBlock_inner]
  exact scalarCoupling_integral _ _ m K hK hm z hz n

end
end Maxwell.Green.PhysicalCompression
