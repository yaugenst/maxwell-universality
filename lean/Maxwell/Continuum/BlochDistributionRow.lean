import Maxwell.Continuum.BlochPeriodicMaterial
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-! A polynomially growing matrix row acting on L² fields is identified
with its literal locally integrable function. Cancellation between entries
is retained; individual weighted entries need not be globally L². -/

noncomputable section

namespace Maxwell.Continuum.Bloch

open MeasureTheory
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false

variable {ι : Type*} [Fintype ι]

def distributionRow (g : ι → Space → ℂ) (u : ι → ScalarL2) : ScalarDistribution :=
  ∑ j, TemperedDistribution.smulLeftCLM ℂ (g j) (Lp.toTemperedDistribution (u j))

def rowValue (g : ι → Space → ℂ) (u : ι → ScalarL2) (x : Space) : ℂ :=
  ∑ j, g j x * u j x

theorem rowValue_locallyIntegrable (g : ι → Space → ℂ)
    (hg : ∀ j, (g j).HasTemperateGrowth) (u : ι → ScalarL2) :
    LocallyIntegrable (rowValue g u) (volume : Measure Space) := by
  apply locallyIntegrable_finsetSum Finset.univ
  intro j _
  exact LocallyIntegrable.continuous_mul (hg j).1.continuous
    ((Lp.memLp (u j)).locallyIntegrable (by norm_num))

theorem row_test_integrable (g : Space → ℂ) (hg : g.HasTemperateGrowth)
    (u : ScalarL2) (φ : SchwartzMap Space ℂ) :
    Integrable (fun x => φ x * (g x * u x)) (volume : Measure Space) := by
  have h := ((SchwartzMap.smulLeftCLM ℂ g φ).memLp 2 volume).integrable_mul (Lp.memLp u)
  convert h using 1
  funext x
  simp only [Pi.mul_apply]
  rw [SchwartzMap.smulLeftCLM_apply_apply hg]
  change φ x * (g x * u x) = (g x * φ x) * u x
  ring

theorem distributionRow_apply (g : ι → Space → ℂ)
    (hg : ∀ j, (g j).HasTemperateGrowth) (u : ι → ScalarL2)
    (φ : SchwartzMap Space ℂ) :
    distributionRow g u φ = ∫ x, φ x * rowValue g u x := by
  simp only [distributionRow, sum_apply, TemperedDistribution.smulLeftCLM_apply_apply,
    Lp.toTemperedDistribution_apply, SchwartzMap.smulLeftCLM_apply_apply (hg _),
    smul_eq_mul, rowValue, Finset.mul_sum]
  rw [integral_finsetSum Finset.univ (fun j _ => row_test_integrable (g j) (hg j) (u j) φ)]
  apply Finset.sum_congr rfl
  intro j _
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by ring

/-- Exact distribution/function equivalence for a finite matrix row. No
individual polynomially weighted component is assumed to belong to L². -/
theorem distributionRow_eq_iff (g : ι → Space → ℂ)
    (hg : ∀ j, (g j).HasTemperateGrowth) (u : ι → ScalarL2) (v : ScalarL2) :
    distributionRow g u = Lp.toTemperedDistribution v ↔ rowValue g u =ᵐ[volume] v := by
  constructor
  · intro h
    apply ae_eq_of_integral_contDiff_smul_eq (rowValue_locallyIntegrable g hg u)
      ((Lp.memLp v).locallyIntegrable (by norm_num))
    intro φ hφ hc
    let ψ : SchwartzMap Space ℂ :=
      (hc.comp_left (show Complex.ofReal 0 = 0 from Complex.ofReal_zero)).toSchwartzMap
        (Complex.ofRealCLM.contDiff.comp hφ)
    have he := congrArg (fun T : ScalarDistribution => T ψ) h
    rw [distributionRow_apply g hg u ψ, Lp.toTemperedDistribution_apply] at he
    change (∫ x, (φ x : ℂ) * rowValue g u x) = (∫ x, (φ x : ℂ) • v x) at he
    simpa only [Complex.real_smul, smul_eq_mul] using he
  · intro h
    ext φ
    rw [distributionRow_apply g hg u φ, Lp.toTemperedDistribution_apply]
    apply integral_congr_ae
    filter_upwards [h] with x hx
    simp only [hx, smul_eq_mul]

end Maxwell.Continuum.Bloch
