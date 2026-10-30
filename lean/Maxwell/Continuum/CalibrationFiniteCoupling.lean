import Maxwell.Continuum.CalibrationFiniteEigenvalue
import Maxwell.Continuum.CalibrationSupercellOffsiteRounded
import Maxwell.Continuum.CalibrationPlacementRadius
import Maxwell.Continuum.CalibrationCouplingRounded

/-! A literal finite rational algorithm for each of the three actual
useful continuum couplings. All aliases, physical translations, and
periodization errors are discharged before the scalar interval is emitted. -/

set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace Maxwell.Continuum.Calibration.FiniteAlgorithm

open FreeFiber Supercell EffectiveMass MasterConstants

attribute [local irreducible] mode size realMode muH roundedTranslatedSandwich
  physicalWellBlock EffectiveMass.wellInteraction

def translatedModeImage (L r N : ℕ) (z : ℚ) (a : Alias) : FourierData :=
  finiteTranslatedSandwich (size L r N) (scale L r N) z 0 a
    (precision L r N) (rootBits L r N) (inverseSteps L r N) (cutoffBits L r N)
    (mode L r N z)

def couplingCenter (L r N : ℕ) (z : ℚ) (a : Alias) : ℚ :=
  (mode L r N z).realInner (translatedModeImage L r N z a)

def couplingEnclosure (L d N : ℕ) (z : ℚ) (j : Fin 3) : RationalInterval :=
  roundedCouplingInterval
    (couplingCenter L (couplingRadius L d) (enclosureModePrecision L N) z
      (placementCell L d (Pi.single j 1))) N

theorem couplingEnclosure_width (L d N : ℕ) (z : ℚ) (j : Fin 3) :
    (couplingEnclosure L d N z j).width=(1/2 : ℚ)^N := roundedCouplingInterval_width _ _

private theorem value_transport (v w : FourierData) (u : FiberSpace)
    (hv : v=w) (hw : w.value=u) : v.value=u := by rw [hv]; exact hw

theorem translatedModeImage_value {L : ℕ} (hL : Ls≤(L : ℝ)) (r N : ℕ) (z : ℚ)
    (D : Auxiliary.Calibration (L : ℝ)⁻¹ z) (a : Alias) :
    (translatedModeImage L r N z a).value =
      roundedTranslatedSandwich (size L r N) (scale L r N) z 0 D (by norm_num) (by norm_num; positivity)
        a (precision L r N) (rootBits L r N) (inverseSteps L r N) (cutoffBits L r N)
        (mode L r N z).value := by
  exact value_transport _ _ _ rfl
    (finiteTranslatedSandwich_value (size L r N) (length_ge_one hL) (scale L r N) z 0 D
      (by norm_num) (by norm_num; positivity) a (precision L r N+2) (lengthBits L)
      (precision L r N) (rootBits L r N) (inverseSteps L r N) (cutoffBits L r N)
      (lengthBits_bound L) (selected_inverse_steps_lower L r N) (mode L r N z))

theorem couplingCenter_physical {L : ℕ} (hL : Ls≤(L : ℝ)) (r N : ℕ) (z : ℚ)
    (D : Auxiliary.Calibration (L : ℝ)⁻¹ z) (a : Alias) :
    (couplingCenter L r N z a : ℝ)=
      (inner ℂ (embedding (size L r N) (mode L r N z).value)
        (physicalLift (size L r N)
          (roundedTranslatedSandwich (size L r N) (scale L r N) z 0 D
            (by norm_num) (by norm_num; positivity) a
            (precision L r N) (rootBits L r N) (inverseSteps L r N) (cutoffBits L r N))
          (embedding (size L r N) (mode L r N z).value))).re :=
  physical_realInner _ _ _ _ _ rfl (translatedModeImage_value hL r N z D a)

private theorem radius_geometry (L r R M : ℝ) (hr : R≤r)
    (hM : 16*(L+r+1)≤M) : 16*(L+R+1)≤M := by linarith

private theorem translated_physical_zero (M : ℕ) [NeZero M] {L : ℝ} (hL : Ls≤L)
    (s z : ℚ) (hs : 4≤(s : ℝ)) (D : Auxiliary.Calibration L⁻¹ z)
    (hEven : Even M) (a : Alias) (hM : 16*(L+(imageRadius a : ℝ)+1)≤(M : ℝ))
    (hscale : (s : ℝ)=2*(M : ℝ)/L)
    (N W ellRoot ellLength K P : ℕ) (hslog : (s : ℝ)≤(2 : ℝ)^ellRoot)
    (hLlog : L≤(2 : ℝ)^ellLength) (hW : cutoffWorkBits (N+1) ellLength≤W)
    (hK : aliasSteps (W+2) ellLength≤K) (hP : cutoffWorkBits W ellLength≤P)
    (hsize : Cs^4*L*((N : ℝ)+(ellLength : ℝ)+2)^2≤(M : ℝ)) :
    ‖physicalLift M (roundedTranslatedSandwich M s z 0 D
        (by norm_num) (by norm_num; positivity) a W ellRoot K P)-
        EffectiveMass.wellInteraction (σ := 0) D le_rfl (by positivity) (-a)‖≤(1/2 : ℝ)^N := by
  simpa only [Rat.cast_zero] using roundedTranslatedSandwich_physical_error M hL s z 0 hs D
    (by norm_num) (by norm_num; positivity) hEven a hM hscale N W ellRoot ellLength K P
    hslog hLlog hW hK hP hsize

theorem translatedOperator_error {L : ℕ} (hL : Ls≤(L : ℝ)) (r N : ℕ) (z : ℚ)
    (D : Auxiliary.Calibration (L : ℝ)⁻¹ z) (a : Alias) (ha : imageRadius a≤r) :
    ‖physicalLift (size L r N)
        (roundedTranslatedSandwich (size L r N) (scale L r N) z 0 D
          (by norm_num) (by norm_num; positivity) a
          (precision L r N) (rootBits L r N) (inverseSteps L r N) (cutoffBits L r N))-
        EffectiveMass.wellInteraction (σ := 0) D (by norm_num) (by norm_num; positivity) (-a)‖≤
      (1/2 : ℝ)^(workPrecision N+96) := by
  have hL0 : 0<L := by exact_mod_cast length_pos hL
  have hgeom := radius_geometry L r (imageRadius a) (size L r N)
    (by exact_mod_cast ha) (size_geometry L r N)
  exact translated_physical_zero (size L r N) hL
    (scale L r N) z (scale_lower hL0 r N) D
    (size_even L r N) a hgeom (scale_cast L r N)
    (workPrecision N+96) (precision L r N) (rootBits L r N) (lengthBits L)
    (inverseSteps L r N) (cutoffBits L r N) (scale_bound hL0 r N) (lengthBits_bound L)
    (selected_operator_precision L r N) (selected_inverse_steps_lower L r N)
    (selected_cutoff_bits_lower L r N) (size_accuracy L r N)

private theorem coupling_work_guard (N ell : ℕ) :
    N+5≤workPrecision (N+2*ell+8)+96 := by
  unfold workPrecision powerWorkPrecision powerWorkBits targetPrecision
  omega

private theorem operator_rhs_transport (A S T : FieldL2 →L[ℂ] FieldL2)
    {ε : ℝ} (hST : S=T) (h : ‖A-T‖≤ε) : ‖A-S‖≤ε := by rw [hST]; exact h

theorem couplingEnclosure_contains {L : ℕ} (hL : Ls≤(L : ℝ)) (d N : ℕ) (z : ℚ)
    (D : Auxiliary.Calibration (L : ℝ)⁻¹ z) (j : Fin 3) :
    (couplingEnclosure L d N z j).Contains (usefulCoupling hL D d j) := by
  let r := couplingRadius L d
  let J := enclosureModePrecision L N
  let a := placementCell L d (Pi.single j 1)
  let B := physicalLift (size L r J)
    (roundedTranslatedSandwich (size L r J) (scale L r J) z 0 D
      (by norm_num) (by norm_num; positivity) a
      (precision L r J) (rootBits L r J) (inverseSteps L r J) (cutoffBits L r J))
  have hB : ‖B-physicalWellBlock D le_rfl (by positivity) d (Pi.single j 1)‖≤
      (1/2 : ℝ)^(N+5) := by
    apply operator_rhs_transport B _ (EffectiveMass.wellInteraction (σ := 0) D le_rfl (by positivity) (-a))
      (by unfold physicalWellBlock; rfl)
    exact (translatedOperator_error hL r J z D a (couplingRadius_contains L d j)).trans
      (pow_le_pow_of_le_one (by norm_num) (by norm_num) (coupling_work_guard N (lengthBits L)))
  have hc := couplingCenter_physical hL r J z D a
  exact usefulCoupling_rounded_interval hL D d j N (lengthBits L) (lengthBits_bound L) B
    (embedding (size L r J) (mode L r J z).value) (couplingCenter L r J z a)
    (mode_physical_error hL r J z D) hB (by rw [hc,sub_self,abs_zero]; positivity)

#print axioms couplingCenter_physical
#print axioms translatedOperator_error
#print axioms couplingEnclosure_contains
end Maxwell.Continuum.Calibration.FiniteAlgorithm
