import Maxwell.Continuum.CalibrationSupercellPhase

/-! The full supercell Fourier translation and its finite rational
diagonal approximation. All alias coordinates are covered uniformly. -/

namespace Maxwell.Continuum.Calibration.Supercell

open FreeFiber

noncomputable def diagonal (c : Alias → ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hc : ∀ ν, ‖c ν‖ ≤ C) : FiberSpace →L[ℂ] FiberSpace :=
  boundedBlocks (fun ν => c ν • (1 : Polarization →L[ℂ] Polarization)) hC
    (fun ν => by simpa only [norm_smul,norm_one,mul_one] using hc ν)

theorem diagonal_apply (c : Alias → ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hc : ∀ ν, ‖c ν‖ ≤ C) (u : FiberSpace) (ν : Alias) :
    diagonal c hC hc u ν=c ν • u ν := rfl

theorem diagonal_norm (c : Alias → ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hc : ∀ ν, ‖c ν‖ ≤ C) : ‖diagonal c hC hc‖ ≤ C := boundedBlocks_norm_le _ _ _

theorem diagonal_error (c d : Alias → ℂ) {C D ε : ℝ}
    (hC : 0 ≤ C) (hc : ∀ ν, ‖c ν‖ ≤ C) (hD : 0 ≤ D) (hd : ∀ ν, ‖d ν‖ ≤ D)
    (hε : 0 ≤ ε) (he : ∀ ν, ‖c ν-d ν‖ ≤ ε) :
    ‖diagonal c hC hc-diagonal d hD hd‖ ≤ ε := by
  have hid : diagonal c hC hc-diagonal d hD hd=diagonal (fun ν => c ν-d ν) hε he := by
    ext u ν i
    change (c ν • u ν-d ν • u ν) i=((c ν-d ν) • u ν) i
    rw [sub_smul]
  rw [hid]
  exact diagonal_norm _ _ _

variable (M : ℕ) [NeZero M]

noncomputable def exactTranslation (a : Alias) : FiberSpace →L[ℂ] FiberSpace :=
  diagonal (exactPhase M a) zero_le_one (fun ν => (exactPhase_norm M a ν).le)

noncomputable def roundedTranslation (a : Alias) (N : ℕ) : FiberSpace →L[ℂ] FiberSpace :=
  diagonal (fun ν => rationalComplexValue (rationalPhaseCoefficient M a ν N)) (by norm_num)
    (fun ν => rationalPhaseCoefficient_norm M a ν N)

theorem exactTranslation_apply (a : Alias) (u : FiberSpace) (ν : Alias) :
    exactTranslation M a u ν=exactPhase M a ν • u ν := rfl

theorem roundedTranslation_apply (a : Alias) (N : ℕ) (u : FiberSpace) (ν : Alias) :
    roundedTranslation M a N u ν=rationalComplexValue (rationalPhaseCoefficient M a ν N) • u ν := rfl

theorem exactTranslation_norm (a : Alias) : ‖exactTranslation M a‖ ≤ 1 := diagonal_norm _ _ _

theorem roundedTranslation_norm (a : Alias) (N : ℕ) : ‖roundedTranslation M a N‖ ≤ 2 :=
  diagonal_norm _ _ _

theorem roundedTranslation_error (a : Alias) (N : ℕ) :
    ‖roundedTranslation M a N-exactTranslation M a‖ ≤ (1/2 : ℝ)^N :=
  diagonal_error _ _ _ _ _ _ (by positivity) (fun ν => rationalPhaseCoefficient_error M a ν N)

def rationalTranslation (a : Alias) (N : ℕ) (f : RationalAliasField) : RationalAliasField :=
  fun ν i => rationalComplexMul (rationalPhaseCoefficient M a ν N) (f ν i)

omit [NeZero M] in
theorem rationalTranslation_supported (a : Alias) (N : ℕ) {f : RationalAliasField} {R : ℕ}
    (hf : RationalSupported f R) : RationalSupported (rationalTranslation M a N f) R := by
  intro ν hν i
  rw [rationalTranslation,hf ν hν i,rationalComplexMul_zero]

theorem rationalTranslation_represents (a : Alias) (N : ℕ) {f : RationalAliasField} {u : FiberSpace}
    (hf : Represents f u) : Represents (rationalTranslation M a N f) (roundedTranslation M a N u) := by
  intro ν i
  rw [rationalTranslation,rationalComplexMul_value,hf,roundedTranslation_apply]
  rfl

def finiteTranslation (a : Alias) (N : ℕ) (v : FourierData) : FourierData :=
  FourierData.ofSupported (rationalTranslation M a N v.field) v.radius

theorem finiteTranslation_value (a : Alias) (N : ℕ) (v : FourierData) :
    (finiteTranslation M a N v).value=roundedTranslation M a N v.value :=
  FourierData.ofSupported_value (rationalTranslation_supported M a N v.supported)
    (rationalTranslation_represents M a N v.represents)

#print axioms roundedTranslation_error
#print axioms finiteTranslation_value

end Maxwell.Continuum.Calibration.Supercell
