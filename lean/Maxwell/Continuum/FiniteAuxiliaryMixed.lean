import Maxwell.Continuum.FiniteAuxiliaryDecomposition

/-! The mixed blocks contain only off-site coupling and uniform detuning.
The exact local eigenmode and on-site scalar tuning contribute no mixed block. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.FiniteAuxiliary

open Auxiliary EffectiveMass MasterConstants

attribute [local irreducible] realMode Sh muH

variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
theorem brightCoefficient_baseline {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) (f : DefectSpace ι) :
    brightCoefficient (realMode D hh) (baseline D hh f) = 0 := by
  apply PiLp.ext
  intro i
  have he := (realModeData D hh).symmetric (realMode D hh) (f i)
  change inner ℂ (Sh D (realMode D hh)) (f i) = inner ℂ (realMode D hh) (Sh D (f i)) at he
  change inner ℂ (realMode D hh) ((muH D hh : ℂ) • f i-Sh D (f i)) = 0
  rw [inner_sub_right, inner_smul_right, ← he, realMode_eigen, inner_smul_left]
  simp

omit [Fintype ι] in
theorem darkProject_onsite_bright {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) (v : ι → ℝ) (f : BrightSpace ι) :
    darkProject (realMode D hh) (onsiteShift D hh v (bright (realMode D hh) f)) = 0 := by
  apply PiLp.ext
  intro i
  change RankOneBand.project (realMode D hh)
    ((((v i)⁻¹-muH D hh : ℝ) : ℂ) • (f i • realMode D hh)) = 0
  rw [map_smul, map_smul, RankOneBand.project_self, smul_zero, smul_zero]

omit [Fintype ι] in
theorem brightCoefficient_onsite_dark {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) (v : ι → ℝ) (f : DarkSpace ι (realMode D hh)) :
    brightCoefficient (realMode D hh) (onsiteShift D hh v (darkEmbed (realMode D hh) f)) = 0 := by
  apply PiLp.ext
  intro i
  change inner ℂ (realMode D hh)
    ((((v i)⁻¹-muH D hh : ℝ) : ℂ) • RankOneBand.embed (realMode D hh) (f i)) = 0
  have he : inner ℂ (realMode D hh) (RankOneBand.embed (realMode D hh) (f i)) = 0 :=
    RankOneBand.coefficient_embed (f i)
  rw [inner_smul_right, he, mul_zero]

def couplingError {L : ℕ} {z σ : ℝ} (D : Calibration (L : ℝ)⁻¹ z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ ((L : ℝ)⁻¹)^4/64)
    (d : ℕ) (position : ι → Bloch.Alias) : DefectSpace ι →L[ℂ] DefectSpace ι :=
  offsite D d position+
    (compressed (L : ℝ)⁻¹ (centers L d position) (resolvent D hσ0 hσ)-
      compressed (L : ℝ)⁻¹ (centers L d position) (resolvent D le_rfl (by positivity)))

theorem auxiliaryMatrix_coupling_decomposition {L : ℕ} {z σ : ℝ}
    (D : Calibration (L : ℝ)⁻¹ z) (hh : (L : ℝ)⁻¹ ≤ 1/(2 : ℝ)^1024)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ ((L : ℝ)⁻¹)^4/64)
    (d : ℕ) (position : ι → Bloch.Alias) (hinj : Function.Injective position) (v : ι → ℝ) :
    auxiliaryMatrix D hσ0 hσ (centers L d position) v =
      baseline D hh+onsiteShift D hh v-couplingError D hσ0 hσ d position := by
  rw [auxiliaryMatrix_decomposition D hh hσ0 hσ d position hinj v, couplingError]
  abel

theorem couplingError_norm {L d : ℕ} {z σ : ℝ} (hL : Ls ≤ (L : ℝ))
    (D : Calibration (L : ℝ)⁻¹ z) (hσ0 : 0 ≤ σ) (hσ : σ ≤ ((L : ℝ)⁻¹)^4/64)
    (hd : 1 ≤ d) (position : ι → Bloch.Alias) (hinj : Function.Injective position) :
    ‖couplingError D hσ0 hσ d position‖ ≤
      Cs*(L : ℝ)^5*(64*((3 : ℝ)^d)⁻¹+(Fintype.card ι : ℝ)*Real.exp (-cs*(L : ℝ)))+
        16*σ*((L : ℝ)⁻¹^4)⁻¹ := by
  have hdisj : Pairwise fun i j => Disjoint
      (Metric.ball (centers L d position i) ((L : ℝ)⁻¹)⁻¹)
      (Metric.ball (centers L d position j) ((L : ℝ)⁻¹)⁻¹) := by
    simpa only [inv_inv] using centers_disjoint (inv_pos.mp D.h_pos) hd position hinj
  exact (norm_add_le _ _).trans (add_le_add
    (offsite_operator_norm hL D le_rfl (by positivity) hd position hinj)
    (compressed_detuning D hσ0 hσ (centers L d position) hdisj))

theorem actual_mixed_lower_norm {L : ℕ} {z σ : ℝ}
    (D : Calibration (L : ℝ)⁻¹ z) (hh : (L : ℝ)⁻¹ ≤ 1/(2 : ℝ)^1024)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ ((L : ℝ)⁻¹)^4/64)
    (d : ℕ) (position : ι → Bloch.Alias) (hinj : Function.Injective position) (v : ι → ℝ) :
    ‖(darkProject (realMode D hh)).comp
      ((auxiliaryMatrix D hσ0 hσ (centers L d position) v).comp (bright (realMode D hh)))‖ ≤
      ‖couplingError D hσ0 hσ d position‖ := by
  have he : (darkProject (realMode D hh)).comp
      ((auxiliaryMatrix D hσ0 hσ (centers L d position) v).comp (bright (realMode D hh))) =
      -((darkProject (realMode D hh)).comp
        ((couplingError D hσ0 hσ d position).comp (bright (realMode D hh)))) := by
    apply ContinuousLinearMap.ext
    intro f
    rw [auxiliaryMatrix_coupling_decomposition D hh hσ0 hσ d position hinj v]
    simp only [ContinuousLinearMap.comp_apply, sub_apply, add_apply, map_sub, map_add,
      baseline_bright, map_zero, darkProject_onsite_bright, add_zero, zero_sub, neg_apply]
  have hn := congrArg norm he
  have hP := darkProject_norm_le (ι := ι) (realMode D hh)
  have hU := bright_norm_le (ι := ι) (realMode D hh) (realMode_norm D hh)
  have hc := contractive_compression_norm (darkProject (ι := ι) (realMode D hh))
    (couplingError D hσ0 hσ d position) (bright (ι := ι) (realMode D hh)) hP hU
  exact hn.trans_le ((_root_.norm_neg _).trans_le hc)

theorem actual_mixed_upper_norm {L : ℕ} {z σ : ℝ}
    (D : Calibration (L : ℝ)⁻¹ z) (hh : (L : ℝ)⁻¹ ≤ 1/(2 : ℝ)^1024)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ ((L : ℝ)⁻¹)^4/64)
    (d : ℕ) (position : ι → Bloch.Alias) (hinj : Function.Injective position) (v : ι → ℝ) :
    ‖(brightCoefficient (realMode D hh)).comp
      ((auxiliaryMatrix D hσ0 hσ (centers L d position) v).comp (darkEmbed (realMode D hh)))‖ ≤
      ‖couplingError D hσ0 hσ d position‖ := by
  have he : (brightCoefficient (realMode D hh)).comp
      ((auxiliaryMatrix D hσ0 hσ (centers L d position) v).comp (darkEmbed (realMode D hh))) =
      -((brightCoefficient (realMode D hh)).comp
        ((couplingError D hσ0 hσ d position).comp (darkEmbed (realMode D hh)))) := by
    apply ContinuousLinearMap.ext
    intro f
    rw [auxiliaryMatrix_coupling_decomposition D hh hσ0 hσ d position hinj v]
    simp only [ContinuousLinearMap.comp_apply, sub_apply, add_apply, map_sub, map_add,
      brightCoefficient_baseline, brightCoefficient_onsite_dark, add_zero, zero_sub, neg_apply]
  have hn := congrArg norm he
  have hP := brightCoefficient_norm_le (ι := ι) (realMode D hh) (realMode_norm D hh)
  have hZ := darkEmbed_norm_le (ι := ι) (realMode D hh)
  have hc := contractive_compression_norm (brightCoefficient (ι := ι) (realMode D hh))
    (couplingError D hσ0 hσ d position) (darkEmbed (ι := ι) (realMode D hh)) hP hZ
  exact hn.trans_le ((_root_.norm_neg _).trans_le hc)

#print axioms actual_mixed_lower_norm
#print axioms actual_mixed_upper_norm

end Maxwell.Continuum.FiniteAuxiliary
