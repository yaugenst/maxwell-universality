import Maxwell.Continuum.FiniteAuxiliaryCoordinates
import Maxwell.Continuum.EffectiveMassRealMode

/-! The complementary gap for every repeated physical well. It is
derived from the actual effective-mass eigenmode and controls the full
infinite-dimensional complementary direct sum. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.FiniteAuxiliary

open Auxiliary EffectiveMass RankOneBand

attribute [local irreducible] realMode Sh muH Well.gap

variable {ι : Type*} [Fintype ι]

def baseline {h z : ℝ} (D : Calibration h z) (hh : h ≤ 1/(2 : ℝ)^1024) :
    DefectSpace ι →L[ℂ] DefectSpace ι :=
  diagonalBlocks (fun _ => (muH D hh : ℂ) • (1 : FieldL2 →L[ℂ] FieldL2)-Sh D)

def darkBaseline {h z : ℝ} (D : Calibration h z) (hh : h ≤ 1/(2 : ℝ)^1024) :
    DarkSpace ι (realMode D hh) →L[ℂ] DarkSpace ι (realMode D hh) :=
  diagonalBlocks (fun _ => baseHigh (Sh D) (realMode D hh) (muH D hh))

omit [Fintype ι] in
theorem modeGap_le_dataGap {h z : ℝ} (_D : Calibration h z) :
    modeGap h ≤ (h^2)⁻¹*(Well.gap/4) := by
  rw [modeGap, Well.gap_exact]
  have hc : ((2 : ℝ)^192)⁻¹ ≤ (1/(2 : ℝ)^188)/4 := by norm_num
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hc (inv_nonneg.mpr (sq_nonneg h))

omit [Fintype ι] in
theorem localBaseline_coercive {h z : ℝ} (D : Calibration h z) (hh : h ≤ 1/(2 : ℝ)^1024) :
    CoerciveInverse.Coercive (baseHigh (Sh D) (realMode D hh) (muH D hh)) (modeGap h) := by
  intro x
  change modeGap h*‖x‖^2 ≤
    (inner ℂ x ((highSpace (realMode D hh)).orthogonalProjectionOnto
      ((muH D hh : ℂ) • (x : FieldL2)-Sh D x))).re
  rw [(highSpace (realMode D hh)).inner_orthogonalProjectionOnto_eq_of_mem_left,
    TopEigenPerturbation.inner_mass_sub]
  change modeGap h*‖x‖^2 ≤ muH D hh*‖x‖^2-(inner ℂ (x : FieldL2) (Sh D x)).re
  have he := (realModeData D hh).complement_energy x
    (Submodule.mem_orthogonal_singleton_iff_inner_right.mp x.property)
  have hg := mul_le_mul_of_nonneg_right (modeGap_le_dataGap D) (sq_nonneg ‖x‖)
  change (inner ℂ (x : FieldL2) (Sh D x)).re ≤
    (muH D hh-(h^2)⁻¹*(Well.gap/4))*‖x‖^2 at he
  nlinarith only [he, hg]

theorem darkBaseline_coercive {h z : ℝ} (D : Calibration h z) (hh : h ≤ 1/(2 : ℝ)^1024) :
    CoerciveInverse.Coercive (darkBaseline (ι := ι) D hh) (modeGap h) := by
  intro x
  rw [PiLp.norm_sq_eq_of_L2, Finset.mul_sum, PiLp.inner_apply]
  change _ ≤ Complex.reCLM (∑ i, inner ℂ (x i) (darkBaseline D hh x i))
  rw [map_sum]
  apply Finset.sum_le_sum
  intro i _
  exact localBaseline_coercive D hh (x i)

def darkBaselineEquiv {h z : ℝ} (D : Calibration h z) (hh : h ≤ 1/(2 : ℝ)^1024) :
    DarkSpace ι (realMode D hh) ≃L[ℂ] DarkSpace ι (realMode D hh) :=
  CoerciveInverse.equiv (darkBaseline D hh) (modeGap_pos D.h_pos) (darkBaseline_coercive D hh)

theorem darkBaseline_inverse_norm {h z : ℝ} (D : Calibration h z) (hh : h ≤ 1/(2 : ℝ)^1024) :
    ‖((darkBaselineEquiv (ι := ι) D hh).symm : DarkSpace ι (realMode D hh) →L[ℂ] DarkSpace ι (realMode D hh))‖ ≤
      (2 : ℝ)^192*h^2 := by
  have he := CoerciveInverse.norm_inverse (darkBaseline (ι := ι) D hh)
    (modeGap_pos D.h_pos) (darkBaseline_coercive D hh)
  change ‖((darkBaselineEquiv (ι := ι) D hh).symm :
    DarkSpace ι (realMode D hh) →L[ℂ] DarkSpace ι (realMode D hh))‖ ≤ _ at he
  exact he.trans_eq (by rw [modeGap, mul_inv_rev, inv_inv, inv_inv, mul_comm])

omit [Fintype ι] in
theorem baseline_dark_compression {h z : ℝ} (D : Calibration h z) (hh : h ≤ 1/(2 : ℝ)^1024) :
    (darkProject (ι := ι) (realMode D hh)).comp ((baseline D hh).comp (darkEmbed (realMode D hh))) =
      darkBaseline D hh := by
  apply ContinuousLinearMap.ext
  intro x
  apply PiLp.ext
  intro i
  rfl

omit [Fintype ι] in
theorem baseline_bright {h z : ℝ} (D : Calibration h z) (hh : h ≤ 1/(2 : ℝ)^1024)
    (f : BrightSpace ι) : baseline D hh (bright (realMode D hh) f) = 0 := by
  apply PiLp.ext
  intro i
  change (muH D hh : ℂ) • (f i • realMode D hh)-Sh D (f i • realMode D hh) = 0
  rw [map_smul, realMode_eigen, smul_comm, sub_self]

#print axioms darkBaseline_coercive
#print axioms darkBaseline_inverse_norm
#print axioms baseline_bright

end Maxwell.Continuum.FiniteAuxiliary
