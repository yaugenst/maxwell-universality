import Maxwell.Continuum.BlochPeriodicMaterial
import Maxwell.Continuum.PeriodicMaterialTranslation

/-! The literal derivative of the prescribed scalar dielectric, as both
an actual physical L² multiplier and an infinite-alias operator. -/

noncomputable section

namespace Maxwell.Continuum.PeriodicMaterial

open Bloch FreeFiber MeasureTheory

def derivativeCoefficient (j : Fin 3) (x : Space) : ℝ :=
  -(2 * backgroundAmplitude * potentialWeight j * Real.pi) * Real.sin (Real.pi * x j)

def derivativeFiber (j : Fin 3) : FiberSpace →L[ℂ] FiberSpace :=
  (((backgroundAmplitude * potentialWeight j * Real.pi : ℝ) : ℂ) * Complex.I) •
    (shift (-unitAlias j) - shift (unitAlias j))

def derivativeMultiplier (j : Fin 3) : FieldL2 →L[ℂ] FieldL2 :=
  (((backgroundAmplitude * potentialWeight j * Real.pi : ℝ) : ℂ) * Complex.I) •
    (fieldModulation (aliasFrequency (unitAlias j)) -
      fieldModulation (aliasFrequency (-unitAlias j)))

theorem coefficient_hasDerivAt (j : Fin 3) (x : Space) :
    HasDerivAt (fun t : ℝ => coefficient (x + t • coordinateDirection j))
      (derivativeCoefficient j x) 0 := by
  have hc (k : Fin 3) : HasDerivAt
      (fun t : ℝ => Real.cos (Real.pi * (x k + t * coordinateDirection j k)))
      (-Real.sin (Real.pi * x k) * (Real.pi * coordinateDirection j k)) 0 := by
    convert ((((hasDerivAt_id (0 : ℝ)).mul_const (coordinateDirection j k)).const_add
      (x k)).const_mul Real.pi).cos using 1 <;> simp
  have hs := HasDerivAt.fun_sum (u := Finset.univ) (fun k _ => (hc k).const_mul (2 * potentialWeight k))
  have ht := (hs.const_mul backgroundAmplitude).const_add 7
  convert ht using 1
  · funext t
    rw [coefficient, periodicPotential_sum]
    rfl
  · fin_cases j <;>
      simp [derivativeCoefficient, coordinateDirection, potentialWeight] <;> ring

theorem phase_pair_sine (x : Space) (j : Fin 3) :
    Complex.I * (phase (aliasFrequency (unitAlias j)) x -
      phase (aliasFrequency (-unitAlias j)) x) = -2 * (Real.sin (Real.pi * x j) : ℂ) := by
  simp only [phase, aliasFrequency_neg, inner_neg_right, inner_aliasFrequency_unitAlias,
    Real.fourierChar_apply]
  have h : 2 * Real.pi * (x j / 2) = Real.pi * x j := by ring
  have hn : 2 * Real.pi * -(x j / 2) = -(Real.pi * x j) := by ring
  rw [h, hn, Complex.ofReal_neg]
  have hs := Complex.two_sin ((Real.pi * x j : ℝ) : ℂ)
  rw [← Complex.ofReal_sin] at hs
  linear_combination hs

theorem derivativeMultiplier_ae (j : Fin 3) (u : FieldL2) (k : Fin 3) :
    derivativeMultiplier j u k =ᵐ[volume]
      fun x => (derivativeCoefficient j x : ℂ) * u k x := by
  let c : ℂ := ((backgroundAmplitude * potentialWeight j * Real.pi : ℝ) : ℂ) * Complex.I
  have he : derivativeMultiplier j u k = c •
      (modulation (aliasFrequency (unitAlias j)) (u k) -
        modulation (aliasFrequency (-unitAlias j)) (u k)) := rfl
  rw [he]
  filter_upwards [Lp.coeFn_smul c (modulation (aliasFrequency (unitAlias j)) (u k) -
      modulation (aliasFrequency (-unitAlias j)) (u k)),
    Lp.coeFn_sub (modulation (aliasFrequency (unitAlias j)) (u k))
      (modulation (aliasFrequency (-unitAlias j)) (u k)),
    modulation_ae (aliasFrequency (unitAlias j)) (u k),
    modulation_ae (aliasFrequency (-unitAlias j)) (u k)] with x hc hs hp hn
  rw [hc]
  change c * ((modulation (aliasFrequency (unitAlias j)) (u k) -
    modulation (aliasFrequency (-unitAlias j)) (u k)) x) = _
  rw [hs]
  simp only [Pi.sub_apply, hp, hn]
  have hphase := phase_pair_sine x j
  unfold derivativeCoefficient c
  push_cast at hphase ⊢
  linear_combination (backgroundAmplitude : ℂ) * (potentialWeight j : ℂ) *
    (Real.pi : ℂ) * (u k x) * hphase

theorem derivativeFiber_norm_le (j : Fin 3) : ‖derivativeFiber j‖ ≤ 28 := by
  have hweight : potentialWeight j ≤ 2 := by fin_cases j <;> norm_num [potentialWeight]
  have hρ : backgroundAmplitude ≤ 1 := backgroundAmplitude_le.trans (by norm_num)
  have hc : 0 ≤ backgroundAmplitude * potentialWeight j * Real.pi :=
    mul_nonneg (mul_nonneg backgroundAmplitude_pos.le (potentialWeight_nonneg j)) Real.pi_pos.le
  have hp : backgroundAmplitude * potentialWeight j * Real.pi ≤ 1 * 2 * 4 :=
    mul_le_mul (mul_le_mul hρ hweight (potentialWeight_nonneg j) (by norm_num))
      Real.pi_lt_four.le Real.pi_pos.le (by norm_num)
  rw [derivativeFiber, norm_smul, norm_mul, Complex.norm_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (mul_nonneg backgroundAmplitude_pos.le (potentialWeight_nonneg j)) Real.pi_pos.le)]
  calc
    _ ≤ (backgroundAmplitude * potentialWeight j * Real.pi) * (1+1) :=
      mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans
        (add_le_add (shift_norm_le _) (shift_norm_le _))) hc
    _ ≤ (1 * 2 * 4) * (1+1) := mul_le_mul_of_nonneg_right hp (by norm_num)
    _ ≤ _ := by norm_num

theorem unitary_derivativeMultiplier_ae (j : Fin 3) (u : FieldL2) :
    unitary (derivativeMultiplier j u) =ᵐ[quasiMeasure]
      fun q => derivativeFiber j (unitary u q) := by
  let c : ℂ := ((backgroundAmplitude * potentialWeight j * Real.pi : ℝ) : ℂ) * Complex.I
  change unitary (c • (fieldModulation (aliasFrequency (unitAlias j)) u -
    fieldModulation (aliasFrequency (-unitAlias j)) u)) =ᵐ[quasiMeasure] _
  rw [map_smul, map_sub, unitary_fieldModulation, unitary_fieldModulation, neg_neg]
  filter_upwards [Lp.coeFn_smul c (aliasShiftL2 (-unitAlias j) (unitary u) -
      aliasShiftL2 (unitAlias j) (unitary u)),
    Lp.coeFn_sub (aliasShiftL2 (-unitAlias j) (unitary u)) (aliasShiftL2 (unitAlias j) (unitary u)),
    aliasShiftL2_ae (-unitAlias j) (unitary u), aliasShiftL2_ae (unitAlias j) (unitary u)]
      with q hc hs hm hp
  rw [hc]
  change c • ((aliasShiftL2 (-unitAlias j) (unitary u) - aliasShiftL2 (unitAlias j) (unitary u)) q) = _
  rw [hs]
  simp only [Pi.sub_apply, hm, hp]
  rfl

theorem derivativeMultiplier_norm_le (j : Fin 3) : ‖derivativeMultiplier j‖ ≤ 28 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro u
  rw [← unitary_norm (derivativeMultiplier j u), ← unitary_norm u]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [unitary_derivativeMultiplier_ae j u] with q hq
  rw [hq]
  exact (derivativeFiber j).le_of_opNorm_le (derivativeFiber_norm_le j) _

#print axioms derivativeMultiplier_ae
#print axioms derivativeMultiplier_norm_le

end Maxwell.Continuum.PeriodicMaterial
