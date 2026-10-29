import Maxwell.Green.PhysicalAnalytic
import Maxwell.Green.CompressedReadout
import Maxwell.Green.SupportedSaddle
import Maxwell.Green.UniformContour

/-! Scalar lower asymptotics for the same finite-support weighted lattice
block as the physical Fourier identity. The local numerator contains the
entire finite-source profile at the moving complex momentum. -/

noncomputable section

namespace Maxwell.Green.PhysicalLower

open Maxwell.Spectral Maxwell.Spectral.Lattice Maxwell.Spectral.Bloch
open SourceProfile PhysicalCompression PhysicalAnalytic Filter Set Metric MeasureTheory InnerProductSpace
open scoped Topology InnerProductSpace ComplexConjugate ContDiff

variable {N : ℕ}

def scalarDensity (edges : Fin N ↪ Edge) (W : Fin N → ℚ)
    (material : Cell20 → ℝ) (E : ℝ) (u : EuclideanSpace ℂ (Fin N))
    (θ : RealTorusCoordinates) (z : ComplexTorusCoordinates) : ℂ :=
  scalarOperatorReadout u (density edges W material E (complexifyCoordinates θ + z))

def sourceNumerator (edges : Fin N ↪ Edge) (W : Fin N → ℚ)
    (u : EuclideanSpace ℂ (Fin N)) (θ : RealTorusCoordinates)
    (P : ComplexTorusCoordinates → EuclideanSpace ℂ Edge20 →L[ℂ] EuclideanSpace ℂ Edge20)
    (z : ComplexTorusCoordinates) : ℂ :=
  scalarCompressedNumerator
    (fun w => sourceLeft edges W (complexifyCoordinates θ + w)) P
    (fun w => sourceRight edges W (complexifyCoordinates θ + w)) u z

theorem sourceNumerator_analyticAt (edges : Fin N ↪ Edge) (W : Fin N → ℚ)
    (u : EuclideanSpace ℂ (Fin N)) (θ : RealTorusCoordinates)
    (P : ComplexTorusCoordinates → EuclideanSpace ℂ Edge20 →L[ℂ] EuclideanSpace ℂ Edge20)
    {z : ComplexTorusCoordinates} (hP : AnalyticAt ℂ P z) :
    AnalyticAt ℂ (sourceNumerator edges W u θ P) z := by
  apply scalarCompressedNumerator_analyticAt
  · exact (sourceLeft_analyticAt edges W _).comp (analyticAt_const.add analyticAt_id)
  · exact hP
  · exact (sourceRight_analyticAt edges W _).comp (analyticAt_const.add analyticAt_id)

theorem sourceNumerator_zero (edges : Fin N ↪ Edge) (W : Fin N → ℚ)
    (u : EuclideanSpace ℂ (Fin N)) (θ : RealTorusCoordinates)
    (P : ComplexTorusCoordinates → EuclideanSpace ℂ Edge20 →L[ℂ] EuclideanSpace ℂ Edge20)
    (φ : EuclideanSpace ℂ Edge20) (hP : P 0 = rankOne ℂ φ φ) :
    sourceNumerator edges W u θ P 0 =
      (‖inner ℂ φ (sourceRight edges W (complexifyCoordinates θ) u)‖ ^ 2 : ℝ) := by
  apply scalarCompressedNumerator_center
    (fun w => sourceLeft edges W (complexifyCoordinates θ + w)) P
    (fun w => sourceRight edges W (complexifyCoordinates θ + w)) u 0
    (sourceRight edges W (complexifyCoordinates θ)) φ
  · change sourceLeft edges W (complexifyCoordinates θ + 0) = _
    rw [add_zero]
    exact sourceLeft_real_adjoint edges W θ
  · exact hP
  · simp only [add_zero]

theorem scalarDensity_analyticAt (edges : Fin N ↪ Edge) (W : Fin N → ℚ)
    (material : Cell20 → ℝ) (E : ℝ) (u : EuclideanSpace ℂ (Fin N))
    (θ : RealTorusCoordinates) {z : ComplexTorusCoordinates}
    (hz : (shiftedOperator material E (complexifyCoordinates θ + z)).IsInvertible) :
    AnalyticAt ℂ (scalarDensity edges W material E u θ) z := by
  exact ((scalarOperatorReadout u).analyticAt _).comp
    ((density_analyticAt edges W material E _ hz).comp (analyticAt_const.add analyticAt_id))

theorem scalarDensity_pole (edges : Fin N ↪ Edge) (W : Fin N → ℚ)
    (material : Cell20 → ℝ) (E : ℝ) (u : EuclideanSpace ℂ (Fin N))
    (θ : RealTorusCoordinates) (lam : ComplexTorusCoordinates → ℂ)
    (P R : ComplexTorusCoordinates → EuclideanSpace ℂ Edge20 →L[ℂ] EuclideanSpace ℂ Edge20)
    (z : ComplexTorusCoordinates)
    (hpole : (shiftedOperator material E (complexifyCoordinates θ + z)).inverse =
      (lam z - (E : ℂ))⁻¹ • P z + R z) :
    scalarDensity edges W material E u θ z =
      sourceNumerator edges W u θ P z / (lam z - (E : ℂ)) +
      sourceNumerator edges W u θ R z := by
  exact scalarCompressedNumerator_pole_decomposition
    (fun w => sourceLeft edges W (complexifyCoordinates θ + w)) P R
    (fun w => (shiftedOperator material E (complexifyCoordinates θ + w)).inverse)
    (fun w => sourceRight edges W (complexifyCoordinates θ + w)) u lam (E : ℂ) z hpole

theorem scalarDensity_periodic (edges : Fin N ↪ Edge) (W : Fin N → ℚ)
    (material : Cell20 → ℝ) (E : ℝ) (u : EuclideanSpace ℂ (Fin N))
    (θ : RealTorusCoordinates) (i : Fin 3) (z : ComplexTorusCoordinates) :
    scalarDensity edges W material E u θ (z + (2 * Real.pi : ℂ) • Pi.single i 1) =
      scalarDensity edges W material E u θ z := by
  unfold scalarDensity
  rw [← add_assoc, density_periodic]

/-- The full torus assembly for the physical weighted source block. Its
quotient identity, smooth regular part, global integrability and majorant
are derived from the actual operator pole identity and ordinary local
spectral estimates. There is no supplied Green asymptotic or localization. -/
theorem exists_physical_torus_assembly
    (edges : Fin N ↪ Edge) (W : Fin N → ℚ) (material : Cell20 → ℝ)
    (E : ℝ) (u : EuclideanSpace ℂ (Fin N)) (θ : RealTorusCoordinates)
    (lam : ComplexTorusCoordinates → ℂ)
    (P R : ComplexTorusCoordinates → EuclideanSpace ℂ Edge20 →L[ℂ] EuclideanSpace ℂ Edge20)
    (center : ComplexTorusCoordinates) (hP : AnalyticAt ℂ P center) (hR : AnalyticAt ℂ R center)
    (hnum : sourceNumerator edges W u θ P center ≠ 0)
    {n : Fin 3 → ℤ} (hn : n ≠ 0)
    (b : OrthonormalBasis (Fin 2) ℝ (transverseSpace (integerMomentum n)))
    (v q₁ q₂ : ℝ) (hv : 0 < v) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hF : AnalyticAt ℂ (affineDenominator lam center
      (principalChart (propagationNormal (integerMomentum n)) (b 0) (b 1)) (E : ℂ)) 0)
    (hFzero : lam center = (E : ℂ))
    (hDu : (fderiv ℂ (affineDenominator lam center
      (principalChart (propagationNormal (integerMomentum n)) (b 0) (b 1)) (E : ℂ)) 0)
      (0, 1) = Complex.I * (v : ℂ))
    (htrans : (fderiv ℂ (affineDenominator lam center
      (principalChart (propagationNormal (integerMomentum n)) (b 0) (b 1)) (E : ℂ)) 0).comp
        (ContinuousLinearMap.inl ℂ (ℂ × ℂ) ℂ) = 0)
    (hquadratic : ∀ w : ℂ,
      -(2 : ℂ)⁻¹ * (Complex.I * (v : ℂ))⁻¹ *
        (fderiv ℂ (fderiv ℂ (affineDenominator lam center
          (principalChart (propagationNormal (integerMomentum n)) (b 0) (b 1)) (E : ℂ))) 0)
          (realTransverse w, 0) (realTransverse w, 0) = quadraticPhase v q₁ q₂ w)
    (hpole : ∀ᶠ z in 𝓝 center, lam z - (E : ℂ) ≠ 0 →
      (shiftedOperator material E (complexifyCoordinates θ + z)).inverse =
        (lam z - (E : ℂ))⁻¹ • P z + R z)
    (hboundary : ∀ q ∈ torusCube (-Real.pi) (2 * Real.pi), q ≠ 0 →
      (shiftedOperator material E
        (complexifyCoordinates θ + (center + complexifyCoordinates q))).IsInvertible)
    (CD : ℝ) (hCD : 0 ≤ CD)
    (hden : ∀ᶠ q in 𝓝 (0 : RealTorusCoordinates), q ≠ 0 →
      lam (center + complexifyCoordinates q) - (E : ℂ) ≠ 0 ∧
      ‖(lam (center + complexifyCoordinates q) - (E : ℂ))⁻¹‖ ≤
        CD * inverseSquare (WithLp.toLp 2 q)) :
    ∃ D : TorusLocalAssemblyData n,
      D.H = (fun q => scalarDensity edges W material E u θ (center + complexifyCoordinates q)) ∧
      D.saddle.amplitude0 = sourceNumerator edges W u θ P center / (Complex.I * (v : ℂ)) ∧
      D.saddle.amplitude0 ≠ 0 ∧ D.normalSpeed = v ∧ D.q₁ = q₁ ∧ D.q₂ = q₂ := by
  let T := principalChart (propagationNormal (integerMomentum n)) (b 0) (b 1)
  let A := sourceNumerator edges W u θ P
  let B := sourceNumerator edges W u θ R
  let F := affineDenominator lam center T (E : ℂ)
  let H := fun q => scalarDensity edges W material E u θ (center + complexifyCoordinates q)
  let Bq := fun q => B (center + complexifyCoordinates q)
  let Aq := fun q => A (center + complexifyCoordinates q)
  have hc : ContDiff ℝ ∞ (fun q : RealTorusCoordinates => center + complexifyCoordinates q) :=
    contDiff_const.add complexifyCLM.contDiff
  have hcont : ContinuousAt (fun q : RealTorusCoordinates => center + complexifyCoordinates q) 0 :=
    hc.continuous.continuousAt
  have ht : Tendsto (fun q : RealTorusCoordinates => center + complexifyCoordinates q)
      (𝓝 0) (𝓝 center) := by simpa only [← complexifyCLM_apply, map_zero, add_zero] using hcont.tendsto
  have hAa := sourceNumerator_analyticAt edges W u θ P hP
  have hBa := sourceNumerator_analyticAt edges W u θ R hR
  have hAq : ContDiffAt ℝ ∞ Aq 0 := by
    have ha : ContDiffAt ℝ ∞ A (center + complexifyCoordinates 0) := by
      simpa only [← complexifyCLM_apply, map_zero, add_zero] using
        (show ContDiffAt ℝ ∞ A center from hAa.restrictScalars.contDiffAt)
    exact ContDiffAt.comp (g := A) (f := fun q => center + complexifyCoordinates q) 0 ha hc.contDiffAt
  have hBq : ContDiffAt ℝ ∞ Bq 0 := by
    have hb : ContDiffAt ℝ ∞ B (center + complexifyCoordinates 0) := by
      simpa only [← complexifyCLM_apply, map_zero, add_zero] using
        (show ContDiffAt ℝ ∞ B center from hBa.restrictScalars.contDiffAt)
    exact ContDiffAt.comp (g := B) (f := fun q => center + complexifyCoordinates q) 0 hb hc.contDiffAt
  have hH : ∀ q ∈ torusCube (-Real.pi) (2 * Real.pi), q ≠ 0 → ContDiffAt ℝ ∞ H q := by
    intro q hq hq₀
    have hs : ContDiffAt ℝ ∞ (scalarDensity edges W material E u θ)
        (center + complexifyCoordinates q) :=
      (scalarDensity_analyticAt edges W material E u θ (hboundary q hq hq₀)).restrictScalars.contDiffAt
    exact ContDiffAt.comp (g := scalarDensity edges W material E u θ)
      (f := fun q => center + complexifyCoordinates q) q hs hc.contDiffAt
  have hpoleq : ∀ᶠ q in 𝓝 (0 : RealTorusCoordinates), q ≠ 0 →
      H q = (lam (center + complexifyCoordinates q) - (E : ℂ))⁻¹ * Aq q + Bq q := by
    filter_upwards [ht.eventually hpole, hden] with q hp hd hq
    have h := scalarDensity_pole edges W material E u θ lam P R _ (hp (hd hq).1)
    simpa only [H, Aq, Bq, A, B, div_eq_mul_inv, mul_comm] using h
  obtain ⟨C, _, hbound⟩ := exists_majorant_of_local_pole_germ H Aq Bq
    (fun q => lam (center + complexifyCoordinates q) - (E : ℂ))
    (-Real.pi) (2 * Real.pi) CD hCD hAq.continuousAt hBq.continuousAt
    (fun q hq hq₀ => (hH q hq hq₀).continuousAt) hpoleq
    (hden.mono (fun q hq hq₀ => (hq hq₀).2))
  have hres : H =ᶠ[𝓝[≠] (0 : RealTorusCoordinates)] fun q =>
      AnalyticLocalGreenData.principalQuotient
        (A := affineDenominator A center T 0) (F := F)
        (coordinatePrincipalLinearEquiv (integerMomentum n) (integerMomentum_ne_zero hn) b) q + Bq q := by
    filter_upwards [hpoleq.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with q hp hq
    rw [hp hq]
    simp only [AnalyticLocalGreenData.principalQuotient, realChartSlice, F, T,
      affineDenominator_inverse_real, sub_zero, Aq, div_eq_mul_inv, mul_comm]
  have hperiod : ∀ (i : Fin 3) (q : RealTorusCoordinates),
      H (q + (2 * Real.pi) • Pi.single i 1) = H q := by
    intro i q
    have he : center + complexifyCoordinates (q + (2 * Real.pi) • Pi.single i 1) =
        (center + complexifyCoordinates q) + (2 * Real.pi : ℂ) • Pi.single i 1 := by
      ext j
      simp [complexifyCoordinates, Pi.single_apply]
      split_ifs <;> simp_all [add_assoc]
    change scalarDensity edges W material E u θ
      (center + complexifyCoordinates (q + (2 * Real.pi) • Pi.single i 1)) = _
    rw [he]
    exact scalarDensity_periodic edges W material E u θ i (center + complexifyCoordinates q)
  have hdu : (fderiv ℂ F 0) (0, 1) ≠ 0 := by
    rw [hDu]
    exact mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hv.ne')
  obtain ⟨D, hDH, hamp, hDv, hDq₁, hDq₂⟩ := exists_torusLocalAssemblyData_of_analytic hn b
    (affineDenominator A center T 0) F (affineDenominator_analytic hAa T 0) hF
    (by change F 0 = 0; simp only [F, affineDenominator, map_zero, add_zero, hFzero, sub_self])
    hdu htrans hv hq₁ hq₂
    (by intro w; change -(2 : ℂ)⁻¹ * ((fderiv ℂ F 0) (0, 1))⁻¹ *
          (fderiv ℂ (fderiv ℂ F) 0) (realTransverse w, 0) (realTransverse w, 0) = _
        rw [hDu]; exact hquadratic w) H Bq C hH hBq hres hperiod hbound
  have hamp' : D.saddle.amplitude0 = A center / (Complex.I * (v : ℂ)) := by
    have ha₀ : affineDenominator A center T 0 (0, 0) = A center := by
      change affineDenominator A center T 0 0 = A center
      simp only [affineDenominator, map_zero, add_zero, sub_zero]
    rw [ha₀] at hamp
    change D.saddle.amplitude0 = A center / (fderiv ℂ F 0) (0, 1) at hamp
    rwa [hDu] at hamp
  refine ⟨D, hDH, hamp', ?_, hDv, hDq₁, hDq₂⟩
  rw [hamp']
  exact div_ne_zero hnum (mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hv.ne'))

end Maxwell.Green.PhysicalLower
