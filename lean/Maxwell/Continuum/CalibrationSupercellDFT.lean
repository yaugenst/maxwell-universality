import Maxwell.Continuum.CalibrationSupercellCharacters

/-! The finite Bloch transform on cell-valued arrays, with its exact
mean-square normalization. -/

noncomputable section
set_option maxRecDepth 4096

namespace Maxwell.Continuum.Calibration.Supercell

open PeriodicSampling
open scoped InnerProduct

variable (M : ℕ) [NeZero M]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def gridSynthesis (v : Grid M → H) (a : Grid M) : H :=
  ∑ j, Product.character M a j • v j

theorem gridSynthesis_inner (u v : Grid M → H) :
    (∑ a : Grid M, inner ℂ (gridSynthesis M u a) (gridSynthesis M v a))=
      (M : ℂ)^3*∑ j : Grid M, inner ℂ (u j) (v j) := by
  classical
  have hinner (a : Grid M) : inner ℂ (gridSynthesis M u a) (gridSynthesis M v a)=
      ∑ j : Grid M, ∑ k : Grid M,
        star (Product.character M a j)*Product.character M a k*inner ℂ (u j) (v k) := by
    rw [gridSynthesis,gridSynthesis,sum_inner]
    apply Finset.sum_congr rfl
    intro j _
    rw [inner_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [inner_smul_left,inner_smul_right]
    exact (mul_assoc _ _ _).symm
  simp_rw [hinner]
  calc
    _ = ∑ j : Grid M, ∑ k : Grid M,
        (∑ a : Grid M, star (Product.character M a j)*Product.character M a k)*inner ℂ (u j) (v k) := by
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_comm]
    _ = ∑ j : Grid M, (M : ℂ)^3*inner ℂ (u j) (v j) := by
      simp only [character_orthogonality,ite_mul,zero_mul]
      simp
    _ = _ := (Finset.mul_sum _ _ _).symm

def gridFactor : ℝ := (Real.sqrt ((M : ℝ)^3))⁻¹

theorem gridFactor_pos : 0<gridFactor M := by
  have hM : (0 : ℝ)<M := by exact_mod_cast NeZero.pos M
  unfold gridFactor
  positivity

theorem gridFactor_square : gridFactor M^2*(M : ℝ)^3=1 := by
  have hM : (M : ℝ)≠0 := by exact_mod_cast NeZero.ne M
  rw [gridFactor,inv_pow,Real.sq_sqrt (by positivity),inv_mul_cancel₀ (pow_ne_zero _ hM)]

abbrev CellArray (H : Type*) := PiLp 2 (fun _ : Grid M => H)

def gridTransform (u : CellArray M H) : CellArray M H :=
  WithLp.toLp 2 (fun a => (gridFactor M : ℂ) • gridSynthesis M (fun j => u j) a)

theorem gridTransform_inner (u v : CellArray M H) :
    inner ℂ (gridTransform M u) (gridTransform M v)=inner ℂ u v := by
  rw [PiLp.inner_apply,PiLp.inner_apply]
  change (∑ a : Grid M, inner ℂ ((gridFactor M : ℂ) • gridSynthesis M (fun j => u j) a)
    ((gridFactor M : ℂ) • gridSynthesis M (fun j => v j) a))=_
  have hstar : star (gridFactor M : ℂ)=(gridFactor M : ℂ) := Complex.conj_ofReal _
  simp only [inner_smul_left,inner_smul_right,starRingEnd_apply,hstar,
    ← mul_assoc,← Finset.mul_sum]
  rw [gridSynthesis_inner]
  have hf : (gridFactor M : ℂ)*(gridFactor M : ℂ)*(M : ℂ)^3=1 := by
    have h := congrArg (fun x : ℝ => (x : ℂ)) (gridFactor_square M)
    simpa only [Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_natCast,Complex.ofReal_one,pow_two] using h
  rw [← mul_assoc,hf,one_mul]

theorem gridTransform_norm (u : CellArray M H) : ‖gridTransform M u‖=‖u‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sq_eq_re_inner (𝕜 := ℂ),gridTransform_inner,norm_sq_eq_re_inner (𝕜 := ℂ)]

def gridTransformLinear : CellArray M H →ₗ[ℂ] CellArray M H where
  toFun := gridTransform M
  map_add' u v := by
    apply PiLp.ext
    intro a
    simp [gridTransform,gridSynthesis,smul_add,Finset.sum_add_distrib]
  map_smul' c u := by
    apply PiLp.ext
    intro a
    simp only [gridTransform,PiLp.smul_apply,gridSynthesis,
      smul_comm _ c,← Finset.smul_sum,RingHom.id_apply]

def gridTransformIsometry : CellArray M H →ₗᵢ[ℂ] CellArray M H where
  toLinearMap := gridTransformLinear M
  norm_map' := gridTransform_norm M

#print axioms gridTransform_inner
#print axioms gridTransformIsometry

end Maxwell.Continuum.Calibration.Supercell
