import Maxwell.Continuum.FiniteAuxiliaryBlocks
import Maxwell.Continuum.RankOneBandBasic

/-! Repeated bright modes and their complete infinite-dimensional
orthogonal complements, in the actual Hilbert direct-sum norm. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.FiniteAuxiliary

variable {ι : Type*} [Fintype ι]
variable {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G]

def coordinatewise (A : ι → H →L[ℂ] G) :
    PiLp 2 (fun _ : ι => H) →L[ℂ] PiLp 2 (fun _ : ι => G) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => G)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i => (A i).comp (PiLp.proj 2 (fun _ : ι => H) i))

omit [Fintype ι] in
@[simp] theorem coordinatewise_apply (A : ι → H →L[ℂ] G)
    (f : PiLp 2 (fun _ : ι => H)) (i : ι) : coordinatewise A f i = A i (f i) := rfl

theorem coordinatewise_norm_le (A : ι → H →L[ℂ] G) {R : ℝ} (hR : 0 ≤ R)
    (hA : ∀ i, ‖A i‖ ≤ R) : ‖coordinatewise A‖ ≤ R := by
  apply ContinuousLinearMap.opNorm_le_bound _ hR
  intro f
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hR (norm_nonneg f))).mp
  rw [PiLp.norm_sq_eq_of_L2, mul_pow, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) ((A i).le_of_opNorm_le (hA i) (f i)) 2

abbrev BrightSpace (ι : Type*) := EuclideanSpace ℂ ι
abbrev DarkSpace (ι : Type*) (u : H) := PiLp 2 (fun _ : ι => RankOneBand.highSpace u)

def bright (u : H) : BrightSpace ι →L[ℂ] PiLp 2 (fun _ : ι => H) :=
  coordinatewise (fun _ => ContinuousLinearMap.toSpanSingleton ℂ u)

def brightCoefficient (u : H) : PiLp 2 (fun _ : ι => H) →L[ℂ] BrightSpace ι :=
  coordinatewise (fun _ => innerSL ℂ u)

def darkEmbed (u : H) : DarkSpace ι u →L[ℂ] PiLp 2 (fun _ : ι => H) :=
  coordinatewise (fun _ => RankOneBand.embed u)

def darkProject (u : H) : PiLp 2 (fun _ : ι => H) →L[ℂ] DarkSpace ι u :=
  coordinatewise (fun _ => RankOneBand.project u)

omit [Fintype ι] in
@[simp] theorem bright_apply (u : H) (f : BrightSpace ι) (i : ι) :
    bright u f i = f i • u := rfl

omit [Fintype ι] in
@[simp] theorem brightCoefficient_apply (u : H) (f : PiLp 2 (fun _ : ι => H)) (i : ι) :
    brightCoefficient u f i = inner ℂ u (f i) := rfl

omit [Fintype ι] in
@[simp] theorem darkEmbed_apply (u : H) (f : DarkSpace ι u) (i : ι) :
    darkEmbed u f i = RankOneBand.embed u (f i) := rfl

omit [Fintype ι] in
@[simp] theorem darkProject_apply (u : H) (f : PiLp 2 (fun _ : ι => H)) (i : ι) :
    darkProject u f i = RankOneBand.project u (f i) := rfl

theorem bright_norm (u : H) (hu : ‖u‖ = 1) (f : BrightSpace ι) : ‖bright u f‖ = ‖f‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [PiLp.norm_sq_eq_of_L2, bright_apply, norm_smul, hu, mul_one]

theorem bright_norm_le (u : H) (hu : ‖u‖ = 1) : ‖bright (ι := ι) u‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (by intro f; rw [bright_norm u hu, one_mul])

theorem brightCoefficient_norm_le (u : H) (hu : ‖u‖ = 1) :
    ‖brightCoefficient (ι := ι) u‖ ≤ 1 := by
  apply coordinatewise_norm_le _ zero_le_one
  intro i
  simpa only [innerSL_apply_norm, hu] using (le_refl ‖innerSL ℂ u‖)

theorem darkEmbed_norm_le (u : H) : ‖darkEmbed (ι := ι) u‖ ≤ 1 :=
  coordinatewise_norm_le _ zero_le_one (fun _ => RankOneBand.embed_norm_le)

theorem darkProject_norm_le (u : H) : ‖darkProject (ι := ι) u‖ ≤ 1 :=
  coordinatewise_norm_le _ zero_le_one (fun _ => RankOneBand.project_norm_le)

omit [Fintype ι] in
theorem brightCoefficient_bright (u : H) (hu : ‖u‖ = 1) (f : BrightSpace ι) :
    brightCoefficient u (bright u f) = f := by
  apply PiLp.ext
  intro i
  simp only [brightCoefficient_apply, bright_apply, inner_smul_right,
    inner_self_eq_norm_sq_to_K, hu]
  norm_num

omit [Fintype ι] in
theorem brightCoefficient_darkEmbed (u : H) (f : DarkSpace ι u) :
    brightCoefficient u (darkEmbed u f) = 0 := by
  apply PiLp.ext
  intro i
  exact RankOneBand.coefficient_embed (f i)

omit [Fintype ι] in
theorem darkProject_bright (u : H) (f : BrightSpace ι) :
    darkProject u (bright u f) = 0 := by
  apply PiLp.ext
  intro i
  simp only [darkProject_apply, bright_apply, map_smul, RankOneBand.project_self, smul_zero]
  rfl

omit [Fintype ι] in
theorem darkProject_darkEmbed (u : H) (f : DarkSpace ι u) :
    darkProject u (darkEmbed u f) = f := by
  apply PiLp.ext
  intro i
  exact RankOneBand.project_embed (f i)

omit [Fintype ι] in
theorem bright_dark_decomposition (u : H) (hu : ‖u‖ = 1)
    (f : PiLp 2 (fun _ : ι => H)) : bright u (brightCoefficient u f)+darkEmbed u (darkProject u f) = f := by
  apply PiLp.ext
  intro i
  have he : RankOneBand.embed u (RankOneBand.project u (f i)) = f i-inner ℂ u (f i) • u := by
    change ((ℂ ∙ u)ᗮ).starProjection (f i) = _
    rw [Submodule.starProjection_orthogonal]
    change f i-(ℂ ∙ u).starProjection (f i) = _
    rw [Submodule.starProjection_unit_singleton ℂ hu]
  change inner ℂ u (f i) • u+RankOneBand.embed u (RankOneBand.project u (f i)) = f i
  rw [he]
  abel

#print axioms bright_dark_decomposition

end Maxwell.Continuum.FiniteAuxiliary
