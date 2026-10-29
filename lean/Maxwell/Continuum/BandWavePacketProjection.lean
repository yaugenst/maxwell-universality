import Maxwell.Continuum.BandWavePacketLp
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! The explicit orthogonal projection onto a measurable rank-one band.
Its pointwise formula, range, and symmetry are proved on actual L² classes. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.BandWavePacket.SectionData

open MeasureTheory Filter
variable {X H : Type*} [MeasurableSpace X]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {μ : Measure X} {s : Set X} (D : SectionData (H := H) μ s)

def projection : Lp H 2 μ →L[ℂ] Lp H 2 μ := D.productCLM.comp D.coefficientCLM

theorem projection_eq_embedding_analysis (f : Lp H 2 μ) :
    D.projection f = D.embedding (D.analysis f) := rfl

theorem projection_ae (f : Lp H 2 μ) :
    D.projection f =ᵐ[μ] fun x => (inner ℂ (D.value x) (f x)) • D.value x := by
  filter_upwards [D.product_ae (D.coefficient f), D.coefficient_ae f] with x hp hc
  change D.product (D.coefficient f) x = _
  rw [hp, hc]

theorem projection_embedding (f : amplitudes μ s) : D.projection (D.embedding f) = D.embedding f := by
  rw [projection_eq_embedding_analysis, analysis_embedding]

theorem projection_idempotent : D.projection * D.projection = D.projection := by
  apply ContinuousLinearMap.ext
  intro f
  change D.projection (D.projection f) = D.projection f
  conv_lhs => rw [projection_eq_embedding_analysis D f]
  exact D.projection_embedding _

theorem projection_range :
    LinearMap.range D.projection.toLinearMap = LinearMap.range D.embedding.toLinearMap := by
  ext f
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨D.analysis g, rfl⟩
  · rintro ⟨g, rfl⟩
    exact ⟨D.embedding g, D.projection_embedding g⟩

theorem projection_symmetric : D.projection.IsSymmetric := by
  intro f g
  change inner ℂ (D.projection f) g = inner ℂ f (D.projection g)
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [D.projection_ae f, D.projection_ae g] with x hf hg
  rw [hf, hg, inner_smul_left, inner_smul_right, inner_conj_symm]
  exact mul_comm _ _

theorem projection_norm_le (f : Lp H 2 μ) : ‖D.projection f‖ ≤ ‖f‖ :=
  (D.product_norm_le (D.coefficient f)).trans (D.coefficient_norm_le f)

theorem projection_fixed_iff (f : Lp H 2 μ) :
    D.projection f = f ↔ ∀ᵐ x ∂μ, f x ∈ ℂ ∙ D.value x := by
  constructor
  · intro hf
    have h := D.projection_ae f
    rw [hf] at h
    filter_upwards [h] with x hx
    rw [hx]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · intro hf
    apply Lp.ext
    filter_upwards [D.projection_ae f, hf] with x hp hx
    rw [hp]
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hx
    rw [← ha, inner_smul_right, inner_self_eq_norm_sq_to_K]
    by_cases hs : x ∈ s
    · rw [D.unit x hs]
      simp
    · rw [D.zero x hs]
      simp

theorem range_iff (f : Lp H 2 μ) :
    f ∈ LinearMap.range D.embedding.toLinearMap ↔ ∀ᵐ x ∂μ, f x ∈ ℂ ∙ D.value x := by
  rw [← D.projection_fixed_iff]
  constructor
  · rintro ⟨g, rfl⟩
    exact D.projection_embedding g
  · intro hf
    exact ⟨D.analysis f, hf⟩

#print axioms projection_idempotent
#print axioms projection_symmetric
#print axioms range_iff

end Maxwell.Continuum.BandWavePacket.SectionData
