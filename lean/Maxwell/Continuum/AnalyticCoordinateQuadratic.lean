import Maxwell.Continuum.PeriodicBandBilinear

/-! Coordinate evenness diagonalizes the actual second Taylor coefficient
of an analytic function on three complex momentum coordinates. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.AnalyticCoordinateQuadratic

open FreeFiber PeriodicBand Filter
open scoped Topology

def bilinear (p : FormalMultilinearSeries ℂ Momentum ℂ) :
    Momentum →L[ℂ] Momentum →L[ℂ] ℂ :=
  (continuousMultilinearCurryFin1 ℂ Momentum ℂ).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (p 2).curryLeft

theorem bilinear_apply (p : FormalMultilinearSeries ℂ Momentum ℂ) (s t : Momentum) :
    bilinear p s t = p 2 ![s, t] := by
  change p 2 (Fin.cons s (Fin.snoc 0 t)) = p 2 ![s, t]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem coefficient_bilinear {f : Momentum → ℂ} {p : FormalMultilinearSeries ℂ Momentum ℂ}
    (hp : HasFPowerSeriesAt f p 0) (v : Momentum) :
    EvenTaylor.coefficient (fun ζ : ℂ => f (ζ • v)) 2 = bilinear p v v := by
  rw [AnalyticLineCoefficients.coefficient_eq hp, bilinear_apply]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem coefficient_reflect {f : Momentum → ℂ}
    (hsym : ∀ j, (fun q => f (FiberReflection.momentum j q)) =ᶠ[𝓝 0] f)
    (j : Fin 3) (v : Momentum) :
    EvenTaylor.coefficient (fun ζ : ℂ => f (ζ • FiberReflection.momentum j v)) 2 =
      EvenTaylor.coefficient (fun ζ : ℂ => f (ζ • v)) 2 := by
  have ht : Filter.Tendsto (fun ζ : ℂ => ζ • v) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun ζ : ℂ => ζ • v) := by fun_prop
    simpa only [zero_smul] using hc.tendsto (0 : ℂ)
  have he := ht.eventually (hsym j)
  have he' : (fun ζ : ℂ => f (ζ • FiberReflection.momentum j v)) =ᶠ[𝓝 0]
      (fun ζ : ℂ => f (ζ • v)) := by
    filter_upwards [he] with ζ hζ
    simpa only [reflection_smul] using hζ
  unfold EvenTaylor.coefficient
  rw [he'.iteratedDeriv_eq 2]

theorem cross_cancel {f : Momentum → ℂ} {p : FormalMultilinearSeries ℂ Momentum ℂ}
    (hp : HasFPowerSeriesAt f p 0)
    (hsym : ∀ j, (fun q => f (FiberReflection.momentum j q)) =ᶠ[𝓝 0] f)
    (j k : Fin 3) (hjk : j ≠ k) :
    bilinear p (basisVector j) (basisVector k) +
      bilinear p (basisVector k) (basisVector j) = 0 := by
  have he := coefficient_reflect hsym j (basisVector j + basisVector k)
  rw [reflection_add, reflect_basis_same, reflect_basis_other j k hjk,
    coefficient_bilinear hp, coefficient_bilinear hp] at he
  simp only [map_add, map_neg, add_apply, neg_apply] at he
  linear_combination -(1 / 2 : ℂ) * he

theorem diagonal {f : Momentum → ℂ} (hf : AnalyticAt ℂ f 0)
    (hsym : ∀ j, (fun q => f (FiberReflection.momentum j q)) =ᶠ[𝓝 0] f)
    (v : Momentum) :
    EvenTaylor.coefficient (fun ζ : ℂ => f (ζ • v)) 2 =
      ∑ j : Fin 3, EvenTaylor.coefficient (fun ζ : ℂ => f (ζ • basisVector j)) 2 * v j ^ 2 := by
  obtain ⟨p, hp⟩ := hf
  simp_rw [coefficient_bilinear hp]
  have hexp : bilinear p v v = ∑ j : Fin 3, ∑ k : Fin 3,
      v j * v k * bilinear p (basisVector j) (basisVector k) := by
    calc
      _ = bilinear p (∑ j : Fin 3, v j • basisVector j)
          (∑ k : Fin 3, v k • basisVector k) :=
        congrArg₂ (fun s t => bilinear p s t) (basis_expansion v) (basis_expansion v)
      _ = _ := by
        simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro k _
        ring
  rw [hexp]
  simp only [Fin.sum_univ_three]
  have h01 := cross_cancel hp hsym 0 1 (by decide)
  have h02 := cross_cancel hp hsym 0 2 (by decide)
  have h12 := cross_cancel hp hsym 1 2 (by decide)
  linear_combination (v 0 * v 1) * h01 + (v 0 * v 2) * h02 + (v 1 * v 2) * h12

end Maxwell.Continuum.AnalyticCoordinateQuadratic
