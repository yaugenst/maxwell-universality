import Maxwell.Continuum.AuxiliaryResolvent

/-! The actual whole-space cutoff resolvent solves the literal periodic
Maxwell distribution equation. In particular its range belongs to the
maximal L² curl-curl domain. The source is the actual cutoff χ. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.Auxiliary

open FreeFiber PeriodicBand Bloch MeasureTheory

theorem sampledEnergy_sub_seven (z σ : ℝ) :
    sampledEnergy z σ - 7 = ((z + σ : ℝ) : ℂ) := by
  unfold sampledEnergy
  push_cast
  ring

theorem cutoffFiber_shifted_graph {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h ^ 4 / 64) (q : QuasiCell) (f : FiberSpace) :
    (cutoffFiber z σ q f, (cutoff q.val : ℂ) • f +
      ((z + σ : ℝ) : ℂ) • cutoffFiber z σ q f) ∈
      (materialFiber (quasiMomentum q) 7 backgroundAmplitude).graph := by
  have hg := material_graph_energy_shift (quasiMomentum q) (sampledEnergy z σ) 7
    backgroundAmplitude _ _ (cutoffFiber_graph D hσ0 hσ q f)
  rwa [sampledEnergy_sub_seven] at hg

/-- `(A_per - z - σ) Rσ = χ` on physical L², stated using the literal
distributional operator rather than an assumed direct-integral model. -/
theorem resolvent_periodic_equation {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h ^ 4 / 64) (f : FieldL2) :
    WeakPeriodicEquation (resolvent D hσ0 hσ f)
      (cutoffOperator f + ((z + σ : ℝ) : ℂ) • resolvent D hσ0 hσ f) := by
  apply (weakPeriodicEquation_iff_fiber_graph _ _).mpr
  rw [map_add, map_smul]
  filter_upwards [resolvent_ae D hσ0 hσ f, cutoffOperator_ae f,
    Lp.coeFn_add (unitary (cutoffOperator f))
      (((z + σ : ℝ) : ℂ) • unitary (resolvent D hσ0 hσ f)),
    Lp.coeFn_smul ((z + σ : ℝ) : ℂ) (unitary (resolvent D hσ0 hσ f))]
      with q hR hχ ha hs
  simp only [ha, Pi.add_apply, hs, Pi.smul_apply, hR, hχ]
  exact cutoffFiber_shifted_graph D hσ0 hσ q (unitary f q)

theorem resolvent_distribution_identity {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h ^ 4 / 64) (f : FieldL2) :
    curlDistribution (curlDistribution (fieldDistribution (resolvent D hσ0 hσ f))) -
      fieldDistribution (PeriodicMaterial.dielectric.multiplier (resolvent D hσ0 hσ f)) -
      ((z + σ : ℝ) : ℂ) • fieldDistribution (resolvent D hσ0 hσ f) =
      fieldDistribution (cutoffOperator f) := by
  have he := resolvent_periodic_equation D hσ0 hσ f
  unfold WeakPeriodicEquation at he
  rw [map_add, map_smul] at he
  exact sub_eq_iff_eq_add.mpr he

theorem resolvent_mem_maximal_curlCurl_domain {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h ^ 4 / 64) (f : FieldL2) :
    ∃ g : FieldL2,
      curlDistribution (curlDistribution (fieldDistribution (resolvent D hσ0 hσ f))) =
        fieldDistribution g := by
  have he := resolvent_periodic_equation D hσ0 hσ f
  unfold WeakPeriodicEquation at he
  refine ⟨cutoffOperator f + ((z + σ : ℝ) : ℂ) • resolvent D hσ0 hσ f +
    PeriodicMaterial.dielectric.multiplier (resolvent D hσ0 hσ f), ?_⟩
  rw [map_add]
  exact sub_eq_iff_eq_add.mp he

#print axioms resolvent_periodic_equation
#print axioms resolvent_distribution_identity
#print axioms resolvent_mem_maximal_curlCurl_domain
#print axioms resolvent_norm_le_length
#print axioms resolvent_difference_norm_le_length
#print axioms resolvent_selfAdjoint

end Maxwell.Continuum.Auxiliary
