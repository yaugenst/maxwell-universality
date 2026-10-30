import Maxwell.Continuum.FiniteAuxiliaryCoordinates
import Maxwell.Continuum.FiniteAuxiliaryTranslation

/-! Exact norms for translated fields with disjoint physical supports. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.FiniteAuxiliary

open MeasureTheory Bloch

theorem field_inner_eq_zero_of_disjoint {f g : FieldL2} {s t : Set Space}
    (hst : Disjoint s t)
    (hf : ∀ k, ∀ᵐ x ∂volume, x ∉ s → f k x = 0)
    (hg : ∀ k, ∀ᵐ x ∂volume, x ∉ t → g k x = 0) : inner ℂ f g = 0 := by
  rw [PiLp.inner_apply]
  apply Finset.sum_eq_zero
  intro k _
  rw [L2.inner_def]
  apply integral_eq_zero_of_ae
  filter_upwards [hf k, hg k] with x hx hy
  change inner ℂ (f k x) (g k x) = 0
  by_cases hs : x ∈ s
  · rw [hy (fun ht => Set.disjoint_left.mp hst hs ht), inner_zero_right]
  · rw [hx hs, inner_zero_left]

theorem orthogonal_sum_norm_sq {ι H : Type*} [Fintype ι]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (f : ι → H)
    (hf : Pairwise fun i j => inner ℂ (f i) (f j) = 0) :
    ‖∑ i, f i‖^2 = ∑ i, ‖f i‖^2 := by
  classical
  rw [@InnerProductSpace.norm_sq_eq_re_inner ℂ]
  simp only [sum_inner, inner_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · exact (InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) (f i)).symm
  · intro j _ hji
    rw [hf hji]
    rfl
  · simp

variable {ι : Type*} [Fintype ι]

def placedField (r : ι → Space) (a : FieldL2) (g : BrightSpace ι) : FieldL2 :=
  ∑ i, g i • fieldTranslation (-r i) a

theorem translated_supported_ball (r : Space) (R : ℝ) (a : FieldL2)
    (ha : ∀ k, ∀ᵐ x ∂volume, R ≤ ‖x‖ → a k x = 0) (k : Fin 3) :
    ∀ᵐ x ∂volume, x ∉ Metric.ball r R → fieldTranslation (-r) a k x = 0 := by
  have hs := (measurePreserving_add_right volume (-r)).quasiMeasurePreserving.ae
    (ha k)
  filter_upwards [fieldTranslation_ae (-r) a k, hs] with x ht hx hnot
  rw [ht]
  apply hx
  simpa only [Metric.mem_ball, dist_eq_norm, not_lt, sub_eq_add_neg] using hnot

theorem placedField_norm (r : ι → Space) (R : ℝ) (a : FieldL2)
    (ha : ∀ k, ∀ᵐ x ∂volume, R ≤ ‖x‖ → a k x = 0)
    (hdisj : Pairwise fun i j => Disjoint (Metric.ball (r i) R) (Metric.ball (r j) R))
    (g : BrightSpace ι) : ‖placedField r a g‖ = ‖a‖*‖g‖ := by
  have ho : Pairwise fun i j => inner ℂ (fieldTranslation (-r i) a)
      (fieldTranslation (-r j) a) = 0 := by
    intro i j hij
    exact field_inner_eq_zero_of_disjoint (hdisj hij)
      (translated_supported_ball (r i) R a ha) (translated_supported_ball (r j) R a ha)
  have hs := orthogonal_sum_norm_sq (fun i => g i • fieldTranslation (-r i) a) (by
    intro i j hij
    rw [inner_smul_left, inner_smul_right, ho hij, mul_zero, mul_zero])
  apply (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp
  change ‖∑ i, g i • fieldTranslation (-r i) a‖^2 = _
  rw [hs, mul_pow, PiLp.norm_sq_eq_of_L2 (x := g), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [norm_smul, (fieldTranslation _).norm_map, mul_pow, mul_comm]

theorem placedField_supported (r : ι → Space) (R : ℝ) (a : FieldL2)
    (ha : ∀ k, ∀ᵐ x ∂volume, R ≤ ‖x‖ → a k x = 0) (g : BrightSpace ι) (k : Fin 3) :
    ∀ᵐ x ∂volume, (∀ i, R ≤ ‖x-r i‖) → placedField r a g k x = 0 := by
  have he : placedField r a g k = ∑ i, g i • fieldTranslation (-r i) a k := by
    simp only [placedField, WithLp.ofLp_sum, Finset.sum_apply]
    rfl
  rw [he]
  have ht : ∀ i, ∀ᵐ x ∂volume, x ∉ Metric.ball (r i) R →
      (g i • fieldTranslation (-r i) a k) x = 0 := by
    intro i
    filter_upwards [translated_supported_ball (r i) R a ha k,
      Lp.coeFn_smul (g i) (fieldTranslation (-r i) a k)] with x hx hc hnot
    rw [hc, Pi.smul_apply, hx hnot, smul_zero]
  filter_upwards [ae_all_iff.mpr ht, Lp.coeFn_finsetSum Finset.univ (fun i => g i • fieldTranslation (-r i) a k)]
    with x hx hs hdist
  change (∑ i, g i • fieldTranslation (-r i) a k) x = 0
  rw [hs, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro i _
  exact hx i (by simpa only [Metric.mem_ball, dist_eq_norm, not_lt] using hdist i)

#print axioms placedField_norm
#print axioms placedField_supported

end Maxwell.Continuum.FiniteAuxiliary
