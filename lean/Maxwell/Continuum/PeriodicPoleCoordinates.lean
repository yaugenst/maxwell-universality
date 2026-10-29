import Maxwell.Continuum.PeriodicPoleGradient

/-! Coordinate insertion for the transverse pole. The longitudinal coordinate
is replaced and the two transverse coordinates are retained literally. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber Set Metric

def poleOffset (j : Fin 3) (w : Momentum) (u : ℂ) : Momentum :=
  fun k => if k = j then u else w k

@[simp] theorem poleOffset_same (j : Fin 3) (w : Momentum) (u : ℂ) : poleOffset j w u j = u := by
  simp only [poleOffset, ite_true]

theorem poleOffset_other (j k : Fin 3) (hkj : k ≠ j) (w : Momentum) (u : ℂ) :
    poleOffset j w u k = w k := by simp only [poleOffset, ite_eq_right hkj]

theorem poleOffset_zero (j : Fin 3) : poleOffset j 0 0 = 0 := by
  funext k
  simp only [poleOffset, Pi.zero_apply, ite_self]

theorem poleOffset_add_basis (j : Fin 3) (w : Momentum) (u : ℂ) :
    poleOffset j w u = poleOffset j w 0 + u • basisVector j := by
  funext k
  simp only [poleOffset, Pi.add_apply, Pi.smul_apply, smul_eq_mul, basisVector_apply]
  split_ifs <;> simp only [mul_one, zero_add, mul_zero, add_zero]

theorem poleOffset_sub (j : Fin 3) (w : Momentum) (u v : ℂ) :
    poleOffset j w u - poleOffset j w v = (u - v) • basisVector j := by
  rw [poleOffset_add_basis j w u, poleOffset_add_basis j w v, sub_smul]
  abel

theorem poleOffset_norm_le {R : ℝ} (hR : 0 ≤ R) (j : Fin 3) {w : Momentum} {u : ℂ}
    (hw : ‖w‖ ≤ R) (hu : ‖u‖ ≤ R) : ‖poleOffset j w u‖ ≤ R := by
  apply (pi_norm_le_iff_of_nonneg hR).mpr
  intro k
  by_cases hkj : k = j
  · subst k
    simpa only [poleOffset_same] using hu
  · simpa only [poleOffset_other j k hkj] using (norm_le_pi_norm w k).trans hw

theorem poleOffset_zero_norm_le (j : Fin 3) (w : Momentum) :
    ‖poleOffset j w 0‖ ≤ ‖w‖ :=
  poleOffset_norm_le (norm_nonneg _) j le_rfl (by simp)

theorem poleOffset_analytic (j : Fin 3) (p : Momentum × ℂ) :
    AnalyticAt ℂ (fun a : Momentum × ℂ => poleOffset j a.1 a.2) p := by
  apply AnalyticAt.pi
  intro k
  by_cases hkj : k = j
  · simpa only [poleOffset, ite_eq_left hkj] using (analyticAt_snd : AnalyticAt ℂ Prod.snd p)
  · have hc := ((ContinuousLinearMap.proj k : Momentum →L[ℂ] ℂ).analyticAt p.1).comp
      (f := Prod.fst) analyticAt_fst
    simpa only [poleOffset, ite_eq_right hkj, Function.comp_def, ContinuousLinearMap.proj_apply] using hc

theorem poleOffset_hasDerivAt (j : Fin 3) (w : Momentum) (u : ℂ) :
    HasDerivAt (poleOffset j w) (basisVector j) u := by
  have he : poleOffset j w = fun v => poleOffset j w 0 + v • basisVector j :=
    funext (poleOffset_add_basis j w)
  rw [he]
  convert! ((hasDerivAt_id u).smul_const (basisVector j)).const_add (poleOffset j w 0) using 1
  simp only [one_smul]

end Maxwell.Continuum.PeriodicBand
