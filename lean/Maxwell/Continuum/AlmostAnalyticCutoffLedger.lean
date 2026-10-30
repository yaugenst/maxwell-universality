import Maxwell.Continuum.AlmostAnalyticCutoffFrechet
import Maxwell.Continuum.MasterConstantLedger

/-! The actual first32 spatial derivative bounds fit the symbolic
constant ledger without evaluating the master constant. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.AlmostAnalytic

open PeriodicBand MasterConstants

theorem cutoff_frechet_ledger {m : ℕ} (hm : m ≤ 32) :
    (2 : ℝ)^13*((2 : ℝ)^154)^m*(m.factorial : ℝ)^2 ≤ (2 : ℝ)^5261 := by
  have hf : (m.factorial : ℝ) ≤ (2 : ℝ)^160 :=
    (by exact_mod_cast Nat.factorial_le hm : (m.factorial : ℝ) ≤ ((32 : ℕ).factorial : ℝ)).trans
      factorial32_le_power
  calc
    _ ≤ (2 : ℝ)^13*((2 : ℝ)^154)^32*((2 : ℝ)^160)^2 := by
      apply mul_le_mul _ (pow_le_pow_left₀ (by positivity) hf 2) (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hm) (by positivity)
    _ = _ := by rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add]

theorem cutoffTaylor_frechet_32_le {β : Space} (hβ : β ≠ 0) {m : ℕ} (hm : m ≤ 32)
    (q : Space) {s : ℝ} (hs : |s| ≤ 1) :
    ‖iteratedFDeriv ℝ m (fun x => cutoffTaylor (cutoffOrder β) smallRadius x β s) q‖ ≤
      (2 : ℝ)^5261 :=
  (cutoffTaylor_frechet_le hβ m q hs).trans (cutoff_frechet_ledger hm)

theorem cutoffTaylor_frechet_master {β : Space} (hβ : β ≠ 0) {m : ℕ} (hm : m ≤ 32)
    (q : Space) {s : ℝ} (hs : |s| ≤ 1) :
    ‖iteratedFDeriv ℝ m (fun x => cutoffTaylor (cutoffOrder β) smallRadius x β s) q‖ ≤ Cs :=
  (cutoffTaylor_frechet_32_le hβ hm q hs).trans
    (fixed_power_le_Cs (by have := exponent_large; omega))

#print axioms cutoffTaylor_frechet_master

end Maxwell.Continuum.AlmostAnalytic
