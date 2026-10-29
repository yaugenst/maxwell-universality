import Maxwell.Continuum.BlochUnitary
import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-! A measurable unit section defines an actual L² isometry from scalar
amplitudes supported on its chart. The source is a concrete L² subspace. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.BandWavePacket

open MeasureTheory Filter

variable {X H : Type*} [MeasurableSpace X]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable (μ : Measure X) (s : Set X)

def amplitudes : Submodule ℂ (Lp ℂ 2 μ) where
  carrier := {f | ∀ᵐ x ∂μ, x ∉ s → f x = 0}
  zero_mem' := by
    filter_upwards [Lp.coeFn_zero ℂ 2 μ] with x hx
    exact fun _ => hx
  add_mem' := by
    intro f g hf hg
    filter_upwards [hf, hg, Lp.coeFn_add f g] with x hfx hgx hfg
    intro hx
    simp only [hfg, Pi.add_apply, hfx hx, hgx hx, add_zero]
  smul_mem' := by
    intro c f hf
    filter_upwards [hf, Lp.coeFn_smul c f] with x hfx hcf
    intro hx
    simp only [hcf, Pi.smul_apply, hfx hx, smul_zero]

structure SectionData where
  value : X → H
  measurable : AEStronglyMeasurable value μ
  unit : ∀ x ∈ s, ‖value x‖ = 1
  zero : ∀ x ∉ s, value x = 0

variable {μ s}

namespace SectionData

variable (D : SectionData (H := H) μ s)

omit [InnerProductSpace ℂ H] in
theorem norm_le (x : X) : ‖D.value x‖ ≤ 1 := by
  by_cases hx : x ∈ s
  · exact (D.unit x hx).le
  · rw [D.zero x hx, norm_zero]
    norm_num

theorem product_memLp (f : Lp ℂ 2 μ) : MemLp (fun x => f x • D.value x) 2 μ := by
  apply (Lp.memLp f).of_le ((Lp.aestronglyMeasurable f).smul D.measurable)
  exact Eventually.of_forall fun x => by
    change ‖f x • D.value x‖ ≤ ‖f x‖
    rw [norm_smul]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (D.norm_le x) (norm_nonneg (f x))

def product (f : Lp ℂ 2 μ) : Lp H 2 μ := (D.product_memLp f).toLp _

theorem product_ae (f : Lp ℂ 2 μ) : D.product f =ᵐ[μ] fun x => f x • D.value x :=
  MemLp.coeFn_toLp _

def productLinear : Lp ℂ 2 μ →ₗ[ℂ] Lp H 2 μ where
  toFun := D.product
  map_add' f g := by
    apply Lp.ext
    filter_upwards [D.product_ae (f+g), D.product_ae f, D.product_ae g,
      Lp.coeFn_add f g, Lp.coeFn_add (D.product f) (D.product g)] with x hfg hf hg ha hb
    simp only [hfg, hb, ha, Pi.add_apply, hf, hg, add_smul]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [D.product_ae (c • f), D.product_ae f,
      Lp.coeFn_smul c f, Lp.coeFn_smul c (D.product f)] with x hcf hf ha hb
    change D.product (c • f) x = (c • D.product f) x
    simp only [hcf, hb, ha, Pi.smul_apply, hf, smul_eq_mul, smul_smul]

theorem product_norm_le (f : Lp ℂ 2 μ) : ‖D.product f‖ ≤ ‖f‖ := by
  have h : ‖D.product f‖ ≤ 1 * ‖f‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [D.product_ae f] with x hx
    rw [hx, norm_smul, one_mul]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (D.norm_le x) (norm_nonneg (f x))
  simpa only [one_mul] using h

def productCLM : Lp ℂ 2 μ →L[ℂ] Lp H 2 μ :=
  D.productLinear.mkContinuous 1 (fun f => by
    change ‖D.product f‖ ≤ 1 * ‖f‖
    simpa only [one_mul] using D.product_norm_le f)

theorem product_norm (f : amplitudes μ s) : ‖D.product f.val‖ = ‖f‖ := by
  change ‖D.product f.val‖ = ‖f.val‖
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  apply eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _)
  filter_upwards [D.product_ae f.val, f.property] with x hx hf
  rw [hx, norm_smul]
  by_cases hs : x ∈ s
  · rw [D.unit x hs, mul_one]
  · rw [hf hs, norm_zero, zero_mul]

def embedding : amplitudes μ s →ₗᵢ[ℂ] Lp H 2 μ where
  toLinearMap := D.productLinear.comp (amplitudes μ s).subtype
  norm_map' := D.product_norm

theorem embedding_ae (f : amplitudes μ s) :
    D.embedding f =ᵐ[μ] fun x => f.val x • D.value x := D.product_ae f.val

theorem coefficient_memLp (g : Lp H 2 μ) : MemLp (fun x => inner ℂ (D.value x) (g x)) 2 μ := by
  apply (Lp.memLp g).of_le (D.measurable.inner (Lp.aestronglyMeasurable g))
  exact Eventually.of_forall fun x =>
    (norm_inner_le_norm (D.value x) (g x)).trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (D.norm_le x) (norm_nonneg (g x)))

def coefficient (g : Lp H 2 μ) : Lp ℂ 2 μ := (D.coefficient_memLp g).toLp _

theorem coefficient_ae (g : Lp H 2 μ) :
    D.coefficient g =ᵐ[μ] fun x => inner ℂ (D.value x) (g x) := MemLp.coeFn_toLp _

theorem coefficient_supported (g : Lp H 2 μ) : D.coefficient g ∈ amplitudes μ s := by
  filter_upwards [D.coefficient_ae g] with x hx
  intro hs
  rw [hx, D.zero x hs, inner_zero_left]

def coefficientLinear : Lp H 2 μ →ₗ[ℂ] Lp ℂ 2 μ where
  toFun := D.coefficient
  map_add' f g := by
    apply Lp.ext
    filter_upwards [D.coefficient_ae (f+g), D.coefficient_ae f, D.coefficient_ae g,
      Lp.coeFn_add f g, Lp.coeFn_add (D.coefficient f) (D.coefficient g)] with x hfg hf hg ha hb
    simp only [hfg, hb, ha, Pi.add_apply, hf, hg, inner_add_right]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [D.coefficient_ae (c • f), D.coefficient_ae f,
      Lp.coeFn_smul c f, Lp.coeFn_smul c (D.coefficient f)] with x hcf hf ha hb
    change D.coefficient (c • f) x = (c • D.coefficient f) x
    simp only [hcf, hb, ha, Pi.smul_apply, hf, inner_smul_right, smul_eq_mul]

theorem coefficient_norm_le (g : Lp H 2 μ) : ‖D.coefficient g‖ ≤ ‖g‖ := by
  have h : ‖D.coefficient g‖ ≤ 1 * ‖g‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [D.coefficient_ae g] with x hx
    rw [hx, one_mul]
    exact (norm_inner_le_norm (D.value x) (g x)).trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (D.norm_le x) (norm_nonneg (g x)))
  simpa only [one_mul] using h

def coefficientCLM : Lp H 2 μ →L[ℂ] Lp ℂ 2 μ :=
  D.coefficientLinear.mkContinuous 1 (fun g => by
    change ‖D.coefficient g‖ ≤ 1 * ‖g‖
    simpa only [one_mul] using D.coefficient_norm_le g)

def analysis : Lp H 2 μ →L[ℂ] amplitudes μ s :=
  D.coefficientCLM.codRestrict (amplitudes μ s) D.coefficient_supported

theorem analysis_embedding (f : amplitudes μ s) : D.analysis (D.embedding f) = f := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [D.coefficient_ae (D.embedding f), D.embedding_ae f, f.property] with x hc he hf
  change D.coefficient (D.embedding f) x = f.val x
  rw [hc, he, inner_smul_right, inner_self_eq_norm_sq_to_K]
  by_cases hx : x ∈ s
  · rw [D.unit x hx]
    simp
  · rw [hf hx, zero_mul]

#print axioms embedding
#print axioms analysis_embedding

end SectionData
end Maxwell.Continuum.BandWavePacket
