import Maxwell.Continuum.CalibrationFiniteAlgorithm
import Maxwell.Continuum.CalibrationRootOperatorBounds

/-! Error of the literal stored starting vector before the physical
normalization join. The well convolution and finite corner seed errors
are both discharged by their actual rational algorithms. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.Calibration.Supercell

open FreeFiber NormedSpace

attribute [local irreducible] computedRootConvolution CornerBridge.topState rootDegree rootDegreeValue
  FourierData.value FourierData.field

variable (M : ℕ) [NeZero M]

def exactRootSeed (s : ℝ) (hs : 4 ≤ s) : FiberSpace :=
  aliasMultiplier (rootTorus s hs) (Complex.I • injection M 0 CornerBridge.topState.val)

theorem finiteSeed_norm (N : ℕ) : ‖(finiteSeed M N).value‖ ≤ 2 := by
  rw [finiteSeed_value,norm_smul,Complex.norm_I,one_mul,injection_norm]
  exact seedVector_norm N

omit [NeZero M] in
private theorem root_seed_perturbation {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℂ H] (Q Qb : H →L[ℂ] H) (u v w : H) {ε : ℝ}
    (hε : 0 ≤ ε) (hQ : ‖Q‖ ≤ 1) (he : ‖Qb-Q‖ ≤ ε)
    (hv : ‖v‖ ≤ 2) (hvu : ‖v-u‖ ≤ ε) (hw : w=Qb v) : ‖w-Q u‖ ≤ 3*ε := by
  rw [hw]
  have h1 : ‖(Qb-Q) v‖ ≤ 2*ε :=
    ((Qb-Q).le_of_opNorm_le he v).trans
      ((mul_le_mul_of_nonneg_left hv hε).trans_eq (mul_comm _ _))
  have h2 : ‖Q (v-u)‖ ≤ ε :=
    (Q.le_of_opNorm_le hQ (v-u)).trans (by simpa only [one_mul] using hvu)
  have hid : Qb v-Q u=(Qb-Q) v+Q (v-u) := by
    simp only [sub_apply,map_sub]
    abel
  rw [hid]
  exact (norm_add_le _ _).trans (by linarith)

theorem finiteRootSeed_error (s : ℚ) (hs : 4 ≤ (s : ℝ)) (W ell : ℕ)
    (hlog : (s : ℝ) ≤ (2 : ℝ)^ell) :
    ‖(FourierData.rootApply s W ell (finiteSeed M W)).value-exactRootSeed M s hs‖ ≤
      3*(1/2 : ℝ)^W := by
  exact root_seed_perturbation
    (aliasMultiplier (rootTorus (s : ℝ) hs) : FiberSpace →L[ℂ] FiberSpace)
    (computedRootConvolution s W ell : FiberSpace →L[ℂ] FiberSpace)
    (Complex.I • injection M 0 CornerBridge.topState.val : FiberSpace)
    ((finiteSeed M W).value : FiberSpace)
    ((FourierData.rootApply s W ell (finiteSeed M W)).value : FiberSpace)
    (by positivity : 0 ≤ (1/2 : ℝ)^W)
    (exactRootOperator_norm s hs)
    (computedRootOperator_reverse_error s hs W ell hlog)
    (finiteSeed_norm M W) (finiteSeed_error M W)
    (FourierData.rootApply_value s W ell (finiteSeed M W))

theorem finiteRootSeed_normalized_error (s : ℚ) (hs : 4 ≤ (s : ℝ)) (W ell : ℕ)
    (hlog : (s : ℝ) ≤ (2 : ℝ)^ell) {δ : ℝ}
    (hδ : 0 < δ) (hlower : δ ≤ ‖exactRootSeed M s hs‖)
    (hsmall : (1/2 : ℝ)^W ≤ δ/8) :
    ‖(FourierData.normalizeData W (FourierData.rootApply s W ell (finiteSeed M W))).value-
        normalize (exactRootSeed M s hs)‖ ≤ 10*(1/2 : ℝ)^W/δ := by
  let v := FourierData.rootApply s W ell (finiteSeed M W)
  let u := exactRootSeed M s hs
  have he : ‖v.value-u‖ ≤ 3*(1/2 : ℝ)^W := finiteRootSeed_error M s hs W ell hlog
  have hv : δ/2 ≤ ‖v.value‖ := by
    have ht := norm_le_norm_sub_add u v.value
    rw [norm_sub_rev] at ht
    linarith
  have hv0 : v.value ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by positivity) hv)
  have hu0 : u ≠ 0 := norm_pos_iff.mp (hδ.trans_le hlower)
  have hn := (FourierData.normalizeData_error W v (by linarith)).2
  have hn' : ‖(FourierData.normalizeData W v).value-normalize v.value‖ ≤
      4*(1/2 : ℝ)^W/δ := by
    apply hn.trans
    apply (div_le_div_of_nonneg_left (by positivity) (by positivity : 0 < δ/2) hv).trans_eq
    ring
  have hd := normalize_difference v.value u hv0 hu0
  have hd' : ‖normalize v.value-normalize u‖ ≤ 6*(1/2 : ℝ)^W/δ := by
    apply hd.trans
    apply (div_le_div₀ (by positivity)
      (mul_le_mul_of_nonneg_left he (by norm_num : (0 : ℝ) ≤ 2)) hδ hlower).trans_eq
    ring
  exact (norm_sub_le_norm_sub_add_norm_sub _ (normalize v.value) _).trans
    ((add_le_add hn' hd').trans_eq (by ring))

#print axioms finiteRootSeed_error
#print axioms finiteRootSeed_normalized_error

end Maxwell.Continuum.Calibration.Supercell
