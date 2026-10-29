import Maxwell.Spectral.ClusterProjection
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Quantitative two-vector orthonormalization

An explicit two-step Gram--Schmidt construction turns projected approximate
eigenvectors into an exact orthonormal frame in the same spectral subspace.
The estimates account for both projection error and the original Gram defect.
-/

namespace Maxwell.Spectral.ClusterOrthonormalization

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def unitVector (x : E) : E := (‖x‖⁻¹ : ℂ) • x

theorem unitVector_norm {x : E} (hx : x ≠ 0) : ‖unitVector x‖ = 1 :=
  norm_smul_inv_norm hx

theorem norm_smul_unitVector (x : E) : (‖x‖ : ℂ) • unitVector x = x := by
  by_cases hx : x = 0
  · simp [unitVector, hx]
  · have hn : (‖x‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hx)
    simp only [unitVector, smul_smul, mul_inv_cancel₀ hn, one_smul]

theorem unitVector_error {x : E} (hx : x ≠ 0) :
    ‖unitVector x - x‖ = |‖x‖ - 1| := by
  calc
    ‖unitVector x - x‖ = ‖(1 - (‖x‖ : ℂ)) • unitVector x‖ := by
      rw [sub_smul, one_smul, norm_smul_unitVector]
    _ = |‖x‖ - 1| := by
      rw [norm_smul, unitVector_norm hx, mul_one]
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        abs_sub_comm]

omit [InnerProductSpace ℂ E] in
theorem norm_deviation_le (x u : E) (δ η : ℝ)
    (hxu : ‖x - u‖ ≤ δ) (hu : |‖u‖ - 1| ≤ η) : |‖x‖ - 1| ≤ δ + η :=
  (abs_sub_le ‖x‖ ‖u‖ 1).trans
    (add_le_add ((abs_norm_sub_norm_le x u).trans hxu) hu)

theorem unitVector_near {x : E} (u : E) (δ η : ℝ) (hx : x ≠ 0)
    (hxu : ‖x - u‖ ≤ δ) (hu : |‖u‖ - 1| ≤ η) :
    ‖unitVector x - u‖ ≤ 2 * δ + η := by
  have hn := norm_deviation_le x u δ η hxu hu
  have ht := norm_sub_le_norm_sub_add_norm_sub (unitVector x) x u
  rw [unitVector_error hx] at ht
  linarith

def first (a : E) : E := unitVector a

def remainder (a b : E) : E := b - inner ℂ (first a) b • first a

def second (a b : E) : E := unitVector (remainder a b)

def frame (a b : E) : Fin 2 → E := ![first a, second a b]

private theorem inner_first_remainder {a : E} (b : E) (ha : a ≠ 0) :
    inner ℂ (first a) (remainder a b) = 0 := by
  simp only [remainder, inner_sub_right, inner_smul_right,
    inner_self_eq_norm_sq_to_K, first, unitVector_norm ha]
  simp

/-- The explicit Gram--Schmidt construction preserves the two-vector span. -/
theorem frame_span (a b : E) :
    Submodule.span ℂ (Set.range (frame a b)) = Submodule.span ℂ ({a, b} : Set E) := by
  rw [frame, Matrix.range_cons_cons_empty]
  let A := Submodule.span ℂ ({a, b} : Set E)
  let F := Submodule.span ℂ ({first a, second a b} : Set E)
  have haA : a ∈ A := Submodule.subset_span (Set.mem_insert a {b})
  have hbA : b ∈ A := Submodule.subset_span (Set.mem_insert_of_mem a rfl)
  have hfirstA : first a ∈ A := A.smul_mem _ haA
  have hwA : remainder a b ∈ A := A.sub_mem hbA (A.smul_mem _ hfirstA)
  have hsecondA : second a b ∈ A := A.smul_mem _ hwA
  have hfirstF : first a ∈ F := Submodule.subset_span (Set.mem_insert _ _)
  have hsecondF : second a b ∈ F := Submodule.subset_span (Set.mem_insert_of_mem _ rfl)
  have haF : a ∈ F := by
    rw [← norm_smul_unitVector a]
    exact F.smul_mem _ hfirstF
  have hwF : remainder a b ∈ F := by
    rw [← norm_smul_unitVector (remainder a b)]
    exact F.smul_mem _ hsecondF
  have hbF : b ∈ F := by
    have h := F.add_mem hwF (F.smul_mem (inner ℂ (first a) b) hfirstF)
    simpa only [remainder, sub_add_cancel] using h
  apply le_antisymm
  · exact Submodule.span_le.mpr (Set.pair_subset_iff.mpr ⟨hfirstA, hsecondA⟩)
  · exact Submodule.span_le.mpr (Set.pair_subset_iff.mpr ⟨haF, hbF⟩)

/-- Quantitative Gram--Schmidt, including the perturbation from the original
reference vectors. The sharper errors are `3 ε` and `15 ε`. -/
theorem frame_orthonormal_and_close (u v a b : E) (ε : ℝ)
    (hε : 0 ≤ ε) (hsmall : ε ≤ 1 / 32)
    (hu : |‖u‖ - 1| ≤ ε) (hv : |‖v‖ - 1| ≤ ε)
    (huv : ‖inner ℂ u v‖ ≤ ε)
    (ha : ‖a - u‖ ≤ ε) (hb : ‖b - v‖ ≤ ε) :
    Orthonormal ℂ (frame a b) ∧
    Submodule.span ℂ (Set.range (frame a b)) = Submodule.span ℂ ({a, b} : Set E) ∧
    ‖frame a b 0 - u‖ ≤ 3 * ε ∧ ‖frame a b 1 - v‖ ≤ 15 * ε := by
  have hanorm := norm_deviation_le a u ε ε ha hu
  have hapos : 0 < ‖a‖ := by
    have h := (abs_le.mp hanorm).1
    linarith
  have hane : a ≠ 0 := norm_pos_iff.mp hapos
  have hfirst : ‖first a‖ = 1 := unitVector_norm hane
  have hfirsterr : ‖first a - u‖ ≤ 3 * ε := by
    have h := unitVector_near u ε ε hane ha hu
    change ‖unitVector a - u‖ ≤ 3 * ε
    linarith
  have hvupper : ‖v‖ ≤ 4 / 3 := by
    have h := (abs_le.mp hv).2
    linarith
  have hβ : ‖inner ℂ (first a) b‖ ≤ 6 * ε := by
    have hid : inner ℂ (first a) b = inner ℂ (first a) (b - v) +
        inner ℂ (first a - u) v + inner ℂ u v := by
      simp only [inner_sub_left, inner_sub_right]
      ring
    have h1 : ‖inner ℂ (first a) (b - v)‖ ≤ ε := by
      apply (norm_inner_le_norm _ _).trans
      simpa only [hfirst, one_mul] using hb
    have h2 : ‖inner ℂ (first a - u) v‖ ≤ (3 * ε) * (4 / 3) :=
      (norm_inner_le_norm _ _).trans
        (mul_le_mul hfirsterr hvupper (norm_nonneg v) (by positivity))
    rw [hid]
    have ht := norm_add_le (inner ℂ (first a) (b - v) + inner ℂ (first a - u) v)
      (inner ℂ u v)
    have ht' := norm_add_le (inner ℂ (first a) (b - v)) (inner ℂ (first a - u) v)
    linarith
  have hwerr : ‖remainder a b - v‖ ≤ 7 * ε := by
    have hid : remainder a b - v = (b - v) - inner ℂ (first a) b • first a := by
      simp only [remainder]
      abel
    rw [hid]
    have ht := norm_sub_le (b - v) (inner ℂ (first a) b • first a)
    rw [norm_smul, hfirst, mul_one] at ht
    linarith
  have hwnorm := norm_deviation_le (remainder a b) v (7 * ε) ε hwerr hv
  have hwpos : 0 < ‖remainder a b‖ := by
    have h := (abs_le.mp hwnorm).1
    linarith
  have hwne : remainder a b ≠ 0 := norm_pos_iff.mp hwpos
  have hsecond : ‖second a b‖ = 1 := unitVector_norm hwne
  have hseconderr : ‖second a b - v‖ ≤ 15 * ε := by
    have h := unitVector_near v (7 * ε) ε hwne hwerr hv
    dsimp only [second]
    linarith
  have horth : inner ℂ (first a) (second a b) = 0 := by
    simp only [second, unitVector, inner_smul_right, inner_first_remainder b hane, mul_zero]
  refine ⟨?_, frame_span a b, hfirsterr, hseconderr⟩
  rw [orthonormal_iff_ite]
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [frame, horth, inner_eq_zero_symm.mpr horth,
      inner_self_eq_norm_sq_to_K, hfirst, hsecond]

/-- The column synthesis map on the two-dimensional Euclidean trial space. -/
def frameMap (f : Fin 2 → E) : EuclideanSpace ℂ (Fin 2) →L[ℂ] E :=
  ∑ i, InnerProductSpace.rankOne ℂ (f i) (EuclideanSpace.basisFun (Fin 2) ℂ i)

theorem frameMap_apply (f : Fin 2 → E) (x : EuclideanSpace ℂ (Fin 2)) :
    frameMap f x = ∑ i, x i • f i := by
  simp only [frameMap, sum_apply, InnerProductSpace.rankOne_apply, EuclideanSpace.basisFun_inner]

@[simp]
theorem frameMap_basis (f : Fin 2 → E) (i : Fin 2) :
    frameMap f (EuclideanSpace.basisFun (Fin 2) ℂ i) = f i := by
  rw [frameMap_apply]
  simp [EuclideanSpace.basisFun_apply, PiLp.single_apply, ite_smul]

/-- The synthesis map has exactly the span of its columns as range. -/
theorem frameMap_range (f : Fin 2 → E) :
    LinearMap.range (frameMap f).toLinearMap = Submodule.span ℂ (Set.range f) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    rw [ContinuousLinearMap.coe_coe, frameMap_apply]
    apply Submodule.sum_mem
    intro i _
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact ⟨EuclideanSpace.basisFun (Fin 2) ℂ i, frameMap_basis f i⟩

theorem frameMap_inner (f : Fin 2 → E) (hf : Orthonormal ℂ f)
    (x y : EuclideanSpace ℂ (Fin 2)) :
    inner ℂ (frameMap f x) (frameMap f y) = inner ℂ x y := by
  rw [frameMap_apply, frameMap_apply, hf.inner_sum]
  simp only [PiLp.inner_apply, RCLike.inner_apply']

/-- The constructed orthonormal columns give an actual linear isometry. -/
def frameIsometry (f : Fin 2 → E) (hf : Orthonormal ℂ f) :
    EuclideanSpace ℂ (Fin 2) →ₗᵢ[ℂ] E :=
  (frameMap f).toLinearMap.isometryOfInner (frameMap_inner f hf)

@[simp]
theorem frameIsometry_toContinuousLinearMap (f : Fin 2 → E) (hf : Orthonormal ℂ f) :
    (frameIsometry f hf).toContinuousLinearMap = frameMap f := by
  ext x
  rfl

/-- The sharper column estimates combine to an operator error of `16 ε`,
without an additional factor of `sqrt 2`. -/
theorem frameMap_close (u v a b : E) (ε : ℝ)
    (hε : 0 ≤ ε) (hsmall : ε ≤ 1 / 32)
    (hu : |‖u‖ - 1| ≤ ε) (hv : |‖v‖ - 1| ≤ ε)
    (huv : ‖inner ℂ u v‖ ≤ ε)
    (ha : ‖a - u‖ ≤ ε) (hb : ‖b - v‖ ≤ ε) :
    ‖frameMap (frame a b) - frameMap ![u, v]‖ ≤ 16 * ε := by
  have h := frame_orthonormal_and_close u v a b ε hε hsmall hu hv huv ha hb
  let D := frameMap (frame a b) - frameMap ![u, v]
  have h0 : ‖D (EuclideanSpace.basisFun (Fin 2) ℂ 0)‖ ≤ 3 * ε := by
    simpa only [D, sub_apply, frameMap_basis, Matrix.cons_val_zero] using h.2.2.1
  have h1 : ‖D (EuclideanSpace.basisFun (Fin 2) ℂ 1)‖ ≤ 15 * ε := by
    simpa only [D, sub_apply, frameMap_basis, Matrix.cons_val_one, Matrix.cons_val_zero] using h.2.2.2
  have h0sq := (sq_le_sq₀ (norm_nonneg _) (show 0 ≤ 3 * ε by positivity)).mpr h0
  have h1sq := (sq_le_sq₀ (norm_nonneg _) (show 0 ≤ 15 * ε by positivity)).mpr h1
  apply (ClusterProjection.opNorm_le_sqrt_sum_basis (EuclideanSpace.basisFun (Fin 2) ℂ) D).trans
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · rw [Fin.sum_univ_two]
    nlinarith [sq_nonneg ε]

/-- The certified witness accuracy `2⁻³⁹` gives the requested strict
`10⁻¹⁰` bound for the full basis map. -/
theorem frameMap_close_concrete (u v a b : E)
    (hu : |‖u‖ - 1| ≤ (2 : ℝ) ^ (-39 : ℤ))
    (hv : |‖v‖ - 1| ≤ (2 : ℝ) ^ (-39 : ℤ))
    (huv : ‖inner ℂ u v‖ ≤ (2 : ℝ) ^ (-39 : ℤ))
    (ha : ‖a - u‖ ≤ (2 : ℝ) ^ (-39 : ℤ))
    (hb : ‖b - v‖ ≤ (2 : ℝ) ^ (-39 : ℤ)) :
    ‖frameMap (frame a b) - frameMap ![u, v]‖ < 1 / 10000000000 := by
  apply (frameMap_close u v a b ((2 : ℝ) ^ (-39 : ℤ))
    (by norm_num) (by norm_num) hu hv huv ha hb).trans_lt
  norm_num

end
end Maxwell.Spectral.ClusterOrthonormalization
