import Maxwell.Continuum.CalibrationSupercellLiftAlgebra
import Maxwell.Continuum.CalibrationSupercellWell
import Maxwell.Continuum.CalibrationSupercellWellCompression
import Maxwell.Continuum.CalibrationSandwichPrecision

/-! The computed rational supercell sandwich approximates the literal
continuum auxiliary operator on the full physical L² space. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace Maxwell.Continuum.Calibration.Supercell

open FreeFiber CellGauge Auxiliary EffectiveMass MasterConstants

variable (M : ℕ) [NeZero M]

attribute [local irreducible] physicalLift physicalOperator aliasMultiplier exactInverse
  Qh Sh roundedSandwich exactSandwich Auxiliary.fiberResolvent

theorem exactSandwich_physical {L z : ℝ} (hL : Ls≤L)
    (D : Auxiliary.Calibration L⁻¹ z) (hEven : Even M)
    (hM : 16*(L+1)≤(M : ℝ)) (s : ℝ) (hs : 4≤s) (hscale : s=2*(M : ℝ)/L) :
    physicalLift M (exactSandwich M s hs z 0)=periodizedAuxiliary D M := by
  have hQ (u : FiberSpace) : Qh L⁻¹ (embedding M u)=
      embedding M (aliasMultiplier (rootTorus s hs) u) := by
    subst s
    exact Qh_embedding M hEven (length_ge_one hL) hM hs u
  rw [exactSandwich,physicalLift_sandwich M _ _ _ (Qh_selfAdjoint L⁻¹) hQ,
    exactInverse,physicalLift_operator]
  change physicalAuxiliary M D=periodizedAuxiliary D M
  exact physicalAuxiliary_eq_periodized M hL D hEven hM

theorem exactSandwich_physical_error {L z : ℝ} (hL : Ls≤L)
    (D : Auxiliary.Calibration L⁻¹ z) (hEven : Even M)
    (hM : 16*(L+1)≤(M : ℝ)) (s : ℝ) (hs : 4≤s) (hscale : s=2*(M : ℝ)/L)
    (N ell : ℕ) (hlog : L≤(2 : ℝ)^ell)
    (hsize : Cs^4*L*((N : ℝ)+(ell : ℝ)+2)^2≤(M : ℝ)) :
    ‖physicalLift M (exactSandwich M s hs z 0)-Sh D‖≤(1/2 : ℝ)^(N+20) := by
  rw [exactSandwich_physical M hL D hEven hM s hs hscale]
  exact periodizedAuxiliary_requested_error hL D M N ell hM hlog hsize

theorem roundedSandwich_physical_error {L : ℝ} (hL : Ls≤L)
    (s z : ℚ) (hs : 4≤(s : ℝ)) (D : Auxiliary.Calibration L⁻¹ z)
    (hEven : Even M) (hM : 16*(L+1)≤(M : ℝ)) (hscale : (s : ℝ)=2*(M : ℝ)/L)
    (N W ellRoot ellLength K P : ℕ) (hslog : (s : ℝ)≤(2 : ℝ)^ellRoot)
    (hLlog : L≤(2 : ℝ)^ellLength) (hW : cutoffWorkBits (N+1) ellLength≤W)
    (hK : aliasSteps (W+2) ellLength≤K) (hP : cutoffWorkBits W ellLength≤P)
    (hsize : Cs^4*L*((N : ℝ)+(ellLength : ℝ)+2)^2≤(M : ℝ)) :
    ‖physicalLift M (roundedSandwich M s z 0 D (by norm_num) (by norm_num; positivity)
        W ellRoot K P)-Sh D‖≤(1/2 : ℝ)^N := by
  let A := roundedSandwich M s z 0 D (by norm_num) (by norm_num; positivity) W ellRoot K P
  let B := exactSandwich M s hs z 0
  have hAB : ‖physicalLift M A-physicalLift M B‖≤(1/2 : ℝ)^(N+1) := by
    apply (physicalLift_error M A B).trans
    rw [norm_sub_rev]
    dsimp only [A,B]
    simpa only [Rat.cast_zero] using roundedSandwich_requested_error M (length_ge_one hL) s z 0 hs D
      (by norm_num) (by norm_num; positivity) (N+1) W ellRoot ellLength K P hslog hLlog hW hK hP
  have hBS : ‖physicalLift M B-Sh D‖≤(1/2 : ℝ)^(N+20) :=
    exactSandwich_physical_error M hL D hEven hM s hs hscale N ellLength hLlog hsize
  change ‖physicalLift M A-Sh D‖≤_
  calc
    _ ≤ ‖physicalLift M A-physicalLift M B‖+‖physicalLift M B-Sh D‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (1/2 : ℝ)^(N+1)+(1/2 : ℝ)^(N+20) := add_le_add hAB hBS
    _ ≤ (1/2 : ℝ)^(N+1)+(1/2 : ℝ)^(N+1) := by
      apply add_le_add le_rfl
      exact pow_le_pow_of_le_one (by norm_num : (0 : ℝ)≤1/2)
        (by norm_num : (1/2 : ℝ)≤1) (by omega)
    _ = _ := by rw [pow_succ]; ring

#print axioms exactSandwich_physical
#print axioms roundedSandwich_physical_error

end Maxwell.Continuum.Calibration.Supercell
