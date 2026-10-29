import Maxwell.Continuum.CompactDirectionalIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod

/-! An integrated transport identity for compact spatial integrands.
It follows from the fundamental theorem of calculus and Fubini, with
the spatial derivative eliminated by actual integration by parts. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.AlmostAnalytic

open MeasureTheory Set

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

theorem compact_transport_identity (G D R : ℝ → Space → F) (β : Space)
    (hG : ∀ s ∈ Icc (0 : ℝ) 1, ContDiff ℝ 1 (G s))
    (hGc : ∀ s ∈ Icc (0 : ℝ) 1, HasCompactSupport (G s))
    (hD : ∀ q, IntervalIntegrable (fun s => D s q) volume 0 1)
    (hDprod : Integrable (Function.uncurry D)
      ((volume.restrict (uIoc (0 : ℝ) 1)).prod volume))
    (hR : ∀ s ∈ Icc (0 : ℝ) 1, Integrable (R s))
    (hd : ∀ q, ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt (fun t => G t q) (D s q) s)
    (hcr : ∀ s ∈ Icc (0 : ℝ) 1, ∀ q,
      D s q = Complex.I • fderiv ℝ (G s) q β + R s q) :
    (∫ q, G 1 q) - (∫ q, G 0 q) = ∫ s in (0 : ℝ)..1, ∫ q, R s q := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, by norm_num⟩
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨by norm_num, le_rfl⟩
  have hends (q : Space) : G 1 q - G 0 q = ∫ s in (0 : ℝ)..1, D s q := by
    apply (intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => G t q) _ (hD q)).symm
    intro s hs
    exact hd q s (by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hs)
  calc
    _ = ∫ q, G 1 q - G 0 q := (integral_sub
      ((hG 1 h1).continuous.integrable_of_hasCompactSupport (hGc 1 h1))
      ((hG 0 h0).continuous.integrable_of_hasCompactSupport (hGc 0 h0))).symm
    _ = ∫ q, ∫ s in (0 : ℝ)..1, D s q := integral_congr_ae (Filter.Eventually.of_forall hends)
    _ = ∫ s in (0 : ℝ)..1, ∫ q, D s q := (intervalIntegral_integral_swap hDprod).symm
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro s hs
      dsimp only
      have hs' : s ∈ Icc (0 : ℝ) 1 := by
        simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hs
      have hg := hG s hs'
      have hgc := hGc s hs'
      have hdcont : Continuous (fun q => fderiv ℝ (G s) q β) :=
        (hg.continuous_fderiv (by norm_num)).clm_apply continuous_const
      have hdc : HasCompactSupport (fun q => fderiv ℝ (G s) q β) :=
        (hgc.fderiv ℝ).comp_left (g := fun A : Space →L[ℝ] F => A β) rfl
      have hdi : Integrable (fun q => fderiv ℝ (G s) q β) volume :=
        hdcont.integrable_of_hasCompactSupport hdc
      have hdiC : Integrable (fun q => Complex.I • fderiv ℝ (G s) q β) volume := by
        convert hdi.smul Complex.I using 1
      have he : D s = fun q => Complex.I • fderiv ℝ (G s) q β + R s q := funext (hcr s hs')
      rw [he]
      dsimp only
      rw [integral_add hdiC (hR s hs'), integral_smul,
        integral_directional_eq_zero (G s) hg hgc β, smul_zero, zero_add]

#print axioms compact_transport_identity

end Maxwell.Continuum.AlmostAnalytic
