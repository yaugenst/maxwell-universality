import Maxwell.Green.PrincipalChart
import Maxwell.Green.TorusContour
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Integral.Prod

/-! The principal transverse chart preserves three-dimensional volume.
The resulting change of variables also identifies the physical Fourier phase. -/

noncomputable section

namespace Maxwell.Green

open MeasureTheory WithLp
open scoped InnerProductSpace

def principalFrame (v : MomentumSpace)
    (b : OrthonormalBasis (Fin 2) ℝ (transverseSpace v)) : Fin 3 → MomentumSpace :=
  ![propagationNormal v, (b 0 : MomentumSpace), (b 1 : MomentumSpace)]

theorem principalFrame_orthonormal (v : MomentumSpace) (hv : v ≠ 0)
    (b : OrthonormalBasis (Fin 2) ℝ (transverseSpace v)) :
    Orthonormal ℝ (principalFrame v b) := by
  rw [orthonormal_iff_ite]
  have hb := b.orthonormal
  rw [orthonormal_iff_ite] at hb
  have hn : ⟪propagationNormal v, propagationNormal v⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_sq, propagationNormal_norm v hv]
    norm_num
  have hn₀ := propagationNormal_inner_transverse v (b 0)
  have hn₁ := propagationNormal_inner_transverse v (b 1)
  have h₀n : ⟪(b 0 : MomentumSpace), propagationNormal v⟫_ℝ = 0 :=
    (real_inner_comm _ _).trans hn₀
  have h₁n : ⟪(b 1 : MomentumSpace), propagationNormal v⟫_ℝ = 0 :=
    (real_inner_comm _ _).trans hn₁
  intro i j
  fin_cases i <;> fin_cases j
  · exact hn
  · exact hn₀
  · exact hn₁
  · exact h₀n
  · exact hb 0 0
  · exact hb 0 1
  · exact h₁n
  · exact hb 1 0
  · exact hb 1 1

def principalOrthonormalBasis (v : MomentumSpace) (hv : v ≠ 0)
    (b : OrthonormalBasis (Fin 2) ℝ (transverseSpace v)) : OrthonormalBasis (Fin 3) ℝ MomentumSpace :=
  (basisOfOrthonormalOfCardEqFinrank (principalFrame_orthonormal v hv b) (by simp)).toOrthonormalBasis
    (by simpa using principalFrame_orthonormal v hv b)

@[simp] theorem principalOrthonormalBasis_apply (v : MomentumSpace) (hv : v ≠ 0)
    (b : OrthonormalBasis (Fin 2) ℝ (transverseSpace v)) (i : Fin 3) :
    principalOrthonormalBasis v hv b i = principalFrame v b i := by
  simp [principalOrthonormalBasis]

/-- Reordering the two real components of the transverse complex coordinate
and the normal real coordinate into an ordinary three-dimensional vector. -/
def transverseNormalEquiv : (ℂ × ℝ) ≃ᵐ (Fin 3 → ℝ) :=
  ((MeasurableEquiv.prodComm : (ℂ × ℝ) ≃ᵐ (ℝ × ℂ)).trans
    ((MeasurableEquiv.refl ℝ).prodCongr Complex.measurableEquivPi)).trans
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).symm

theorem transverseNormalEquiv_measurePreserving : MeasurePreserving transverseNormalEquiv := by
  exact (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).symm.comp
    (((MeasurePreserving.id volume).prod Complex.volume_preserving_equiv_pi).comp
      Measure.measurePreserving_swap)

@[simp] theorem transverseNormalEquiv_apply (w : ℂ) (u : ℝ) :
    transverseNormalEquiv (w, u) = ![u, w.re, w.im] := by
  ext i
  fin_cases i <;> rfl

def realPrincipalChart (v : MomentumSpace)
    (b : OrthonormalBasis (Fin 2) ℝ (transverseSpace v)) (z : ℂ × ℝ) : MomentumSpace :=
  z.1.re • (b 0 : MomentumSpace) + z.1.im • (b 1 : MomentumSpace) + z.2 • propagationNormal v

def realPrincipalEquiv (v : MomentumSpace) (hv : v ≠ 0)
    (b : OrthonormalBasis (Fin 2) ℝ (transverseSpace v)) : (ℂ × ℝ) ≃ᵐ MomentumSpace :=
  (transverseNormalEquiv.trans (MeasurableEquiv.toLp 2 (Fin 3 → ℝ))).trans
    (principalOrthonormalBasis v hv b).measurableEquiv.symm

theorem realPrincipalEquiv_measurePreserving (v : MomentumSpace) (hv : v ≠ 0)
    (b : OrthonormalBasis (Fin 2) ℝ (transverseSpace v)) :
    MeasurePreserving (realPrincipalEquiv v hv b) := by
  exact (principalOrthonormalBasis v hv b).measurePreserving_measurableEquiv.symm.comp
    ((PiLp.volume_preserving_toLp (Fin 3)).comp transverseNormalEquiv_measurePreserving)

@[simp] theorem realPrincipalEquiv_apply (v : MomentumSpace) (hv : v ≠ 0)
    (b : OrthonormalBasis (Fin 2) ℝ (transverseSpace v)) (z : ℂ × ℝ) :
    realPrincipalEquiv v hv b z = realPrincipalChart v b z := by
  change (principalOrthonormalBasis v hv b).repr.symm (toLp 2 (transverseNormalEquiv z)) = _
  rw [← OrthonormalBasis.sum_repr_symm]
  rcases z with ⟨w, u⟩
  simp [Fin.sum_univ_succ, principalFrame, realPrincipalChart]
  abel

def realPrincipalLinearMap (v : MomentumSpace)
    (b : OrthonormalBasis (Fin 2) ℝ (transverseSpace v)) : (ℂ × ℝ) →ₗ[ℝ] MomentumSpace where
  toFun := realPrincipalChart v b
  map_add' := by
    intro x y
    simp only [realPrincipalChart, Prod.fst_add, Prod.snd_add, Complex.add_re, Complex.add_im,
      add_smul]
    abel
  map_smul' := by
    intro c x
    simp [realPrincipalChart, smul_add, smul_smul]

def realPrincipalLinearEquiv (v : MomentumSpace) (hv : v ≠ 0)
    (b : OrthonormalBasis (Fin 2) ℝ (transverseSpace v)) : (ℂ × ℝ) ≃L[ℝ] MomentumSpace :=
  (LinearEquiv.ofBijective (realPrincipalLinearMap v b) (by
    change Function.Bijective (realPrincipalChart v b)
    have he : realPrincipalChart v b = realPrincipalEquiv v hv b :=
      funext fun z => (realPrincipalEquiv_apply v hv b z).symm
    rw [he]
    exact (realPrincipalEquiv v hv b).bijective)).toContinuousLinearEquiv

@[simp] theorem realPrincipalLinearEquiv_apply (v : MomentumSpace) (hv : v ≠ 0)
    (b : OrthonormalBasis (Fin 2) ℝ (transverseSpace v)) (z : ℂ × ℝ) :
    realPrincipalLinearEquiv v hv b z = realPrincipalChart v b z := rfl

def coordinatePrincipalLinearEquiv (v : MomentumSpace) (hv : v ≠ 0)
    (b : OrthonormalBasis (Fin 2) ℝ (transverseSpace v)) : (ℂ × ℝ) ≃L[ℝ] RealTorusCoordinates :=
  (realPrincipalLinearEquiv v hv b).trans (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ))

@[simp] theorem coordinatePrincipalLinearEquiv_apply (v : MomentumSpace) (hv : v ≠ 0)
    (b : OrthonormalBasis (Fin 2) ℝ (transverseSpace v)) (z : ℂ × ℝ) :
    coordinatePrincipalLinearEquiv v hv b z = ofLp (realPrincipalChart v b z) := rfl

theorem principalChart_realPrincipalChart (v : MomentumSpace)
    (b : OrthonormalBasis (Fin 2) ℝ (transverseSpace v)) (w : ℂ) (u : ℝ) :
    principalChart (propagationNormal v) (b 0) (b 1) (realTransverse w, (u : ℂ)) =
      momentumComplex (realPrincipalChart v b (w, u)) := by
  ext i
  simp [principalChart, realPrincipalChart, realTransverse, momentumComplex]

/-- The complex principal chart and the inverse real chart agree exactly
on real physical momenta. -/
theorem principalChart_inverse_real (v : MomentumSpace) (hv : v ≠ 0)
    (b : OrthonormalBasis (Fin 2) ℝ (transverseSpace v)) (q : RealTorusCoordinates) :
    let z := (coordinatePrincipalLinearEquiv v hv b).symm q
    principalChart (propagationNormal v) (b 0) (b 1) (realTransverse z.1, (z.2 : ℂ)) =
      complexifyCoordinates q := by
  dsimp only
  rw [principalChart_realPrincipalChart]
  have h := congrArg complexifyCoordinates
    ((coordinatePrincipalLinearEquiv v hv b).apply_symm_apply q)
  exact h

theorem affineDenominator_inverse_real (lam : ComplexTorusCoordinates → ℂ)
    (center : ComplexTorusCoordinates) (energy : ℂ)
    (v : MomentumSpace) (hv : v ≠ 0)
    (b : OrthonormalBasis (Fin 2) ℝ (transverseSpace v)) (q : RealTorusCoordinates) :
    let z := (coordinatePrincipalLinearEquiv v hv b).symm q
    affineDenominator lam center (principalChart (propagationNormal v) (b 0) (b 1)) energy
      (realTransverse z.1, (z.2 : ℂ)) = lam (center + complexifyCoordinates q) - energy := by
  dsimp only [affineDenominator]
  rw [principalChart_inverse_real]

theorem realPrincipalChart_phase (v : MomentumSpace) (hv : v ≠ 0)
    (b : OrthonormalBasis (Fin 2) ℝ (transverseSpace v)) (w : ℂ) (u : ℝ) :
    ⟪v, realPrincipalChart v b (w, u)⟫_ℝ = ‖v‖ * u := by
  have hn := supportGradient_normal v hv 1
  have h₀ := supportGradient_transverse v 1 (b 0)
  have h₁ := supportGradient_transverse v 1 (b 1)
  simp only [one_smul, one_mul] at hn h₀ h₁
  simp [realPrincipalChart, inner_add_right, inner_smul_right, h₀, h₁, hn, mul_comm]

/-- Exact volume change of variables, with no determinant factor. -/
theorem integral_realPrincipalChart (v : MomentumSpace) (hv : v ≠ 0)
    (b : OrthonormalBasis (Fin 2) ℝ (transverseSpace v)) (f : MomentumSpace → ℂ) :
    (∫ z : ℂ × ℝ, f (realPrincipalChart v b z)) = ∫ q : MomentumSpace, f q := by
  simpa using (realPrincipalEquiv_measurePreserving v hv b).integral_comp' f

/-- The local three-dimensional Fourier integral is the transverse-normal
iterated integral used by the residue and Gaussian estimates. -/
theorem integral_fourier_realPrincipalChart (v : MomentumSpace) (hv : v ≠ 0)
    (b : OrthonormalBasis (Fin 2) ℝ (transverseSpace v)) (f : MomentumSpace → ℂ) (d : ℝ)
    (hint : Integrable (fun z : ℂ × ℝ =>
      Complex.exp (Complex.I * ((d * ‖v‖ * z.2 : ℝ) : ℂ)) * f (realPrincipalChart v b z))) :
    (∫ q : MomentumSpace, Complex.exp (Complex.I * ((d * ⟪v, q⟫_ℝ : ℝ) : ℂ)) * f q) =
      ∫ w : ℂ, ∫ u : ℝ, Complex.exp (Complex.I * ((d * ‖v‖ * u : ℝ) : ℂ)) *
        f (realPrincipalChart v b (w, u)) := by
  rw [← integral_realPrincipalChart v hv b]
  simp_rw [realPrincipalChart_phase v hv b, ← mul_assoc]
  exact integral_prod _ hint

def coordinatePrincipalEquiv (v : MomentumSpace) (hv : v ≠ 0)
    (b : OrthonormalBasis (Fin 2) ℝ (transverseSpace v)) :
    (ℂ × ℝ) ≃ᵐ RealTorusCoordinates :=
  (realPrincipalEquiv v hv b).trans (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm

theorem coordinatePrincipalEquiv_measurePreserving (v : MomentumSpace) (hv : v ≠ 0)
    (b : OrthonormalBasis (Fin 2) ℝ (transverseSpace v)) :
    MeasurePreserving (coordinatePrincipalEquiv v hv b) :=
  (PiLp.volume_preserving_ofLp (Fin 3)).comp (realPrincipalEquiv_measurePreserving v hv b)

@[simp] theorem coordinatePrincipalEquiv_apply (v : MomentumSpace) (hv : v ≠ 0)
    (b : OrthonormalBasis (Fin 2) ℝ (transverseSpace v)) (z : ℂ × ℝ) :
    coordinatePrincipalEquiv v hv b z = ofLp (realPrincipalChart v b z) := by
  simp [coordinatePrincipalEquiv]

theorem torusCubeMeasure_eq_restrict (a p : ℝ) :
    torusCubeMeasure a p = volume.restrict (Set.univ.pi (fun _ : Fin 3 => Set.Ioc a (a + p))) := by
  exact (Measure.restrict_pi_pi (fun _ : Fin 3 => volume) _).symm

/-- A localization supported in the fundamental cube has precisely the
same integral in the torus chart and in unrestricted Euclidean space. -/
theorem integral_torus_localization (a p : ℝ) (f : RealTorusCoordinates → ℂ)
    (hs : Function.support f ⊆ Set.univ.pi (fun _ : Fin 3 => Set.Ioc a (a + p))) :
    (∫ q, f q ∂torusCubeMeasure a p) = ∫ q, f q := by
  rw [torusCubeMeasure_eq_restrict]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro q hq
  by_contra h
  exact hq (hs h)

theorem integral_torus_localization_chart (a p : ℝ) (f : RealTorusCoordinates → ℂ)
    (hs : Function.support f ⊆ Set.univ.pi (fun _ : Fin 3 => Set.Ioc a (a + p)))
    (v : MomentumSpace) (hv : v ≠ 0)
    (b : OrthonormalBasis (Fin 2) ℝ (transverseSpace v))
    (hint : Integrable (fun z : ℂ × ℝ => f (ofLp (realPrincipalChart v b z)))) :
    (∫ q, f q ∂torusCubeMeasure a p) =
      ∫ w : ℂ, ∫ u : ℝ, f (ofLp (realPrincipalChart v b (w, u))) := by
  rw [integral_torus_localization a p f hs,
    ← (coordinatePrincipalEquiv_measurePreserving v hv b).integral_comp' f]
  simp only [coordinatePrincipalEquiv_apply]
  exact integral_prod _ hint

end Maxwell.Green
