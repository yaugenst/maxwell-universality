import Maxwell.Cost.BitRAM
import Maxwell.Complexity
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace Maxwell.Cost
open Filter Asymptotics

/-- The retained construction and solver terms, including a fixed
polylogarithmic factor. This is an envelope, not a claimed runtime field. -/
noncomputable def transferEnvelope (θ : ℝ) (logPower : ℕ) (x : ℝ) : ℝ :=
  Real.log x ^ logPower * (x ^ (3 / 2 : ℝ) + x ^ (3 * θ / 2))

/-- Every fixed polylogarithmic factor is absorbed by a strict power gap. -/
theorem polylog_rpow_littleO (a γ : ℝ) (logPower : ℕ) (h : a < γ) :
    (fun x : ℝ => Real.log x ^ logPower * x ^ a) =o[atTop] (fun x => x ^ γ) := by
  have hlog := isLittleO_log_rpow_rpow_atTop (logPower : ℝ) (by linarith : 0 < γ - a)
  have hmul := hlog.mul_isBigO (isBigO_refl (fun x : ℝ => x ^ a) atTop)
  apply hmul.congr'
  · exact Filter.Eventually.of_forall (fun x => by simp)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [← Real.rpow_add hx]
    congr 1
    ring

theorem transferEnvelope_littleO (θ γ : ℝ) (logPower : ℕ)
    (hconstruction : (3 : ℝ) / 2 < γ) (hsolver : θ < 2 * γ / 3) :
    transferEnvelope θ logPower =o[atTop] (fun x => x ^ γ) := by
  have hs : 3 * θ / 2 < γ := by linarith
  have hsum := (polylog_rpow_littleO (3 / 2) γ logPower hconstruction).add
    (polylog_rpow_littleO (3 * θ / 2) γ logPower hs)
  change (fun x : ℝ => Real.log x ^ logPower *
    (x ^ (3 / 2 : ℝ) + x ^ (3 * θ / 2))) =o[atTop] (fun x => x ^ γ)
  simpa only [mul_add] using hsum

/-- Actual finite-code capped runs satisfy the cap on all inputs and tapes.
This uses the operational theorem, not a solver's good-instance promise. -/
theorem bitRAM_capped_runtime_isBigO_cap (machine : BitRAM)
    (input : ℕ → List Bool) (tape : ℕ → ℕ → Bool) (cap : ℕ → ℕ) :
    (fun n => ((machine.run (input n) (tape n) (cap n)).instructions : ℝ))
      =O[atTop] (fun n => (cap n : ℝ)) := by
  apply IsBigO.of_norm_eventuallyLE
  apply Filter.Eventually.of_forall
  intro n
  simp only [Real.norm_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast machine.run_all_inputs_le (input n) (tape n) (cap n)

/-- The exponent transfer is connected to an actual time-capped finite-code
machine. A cap chosen within the two-term bound gives strict `o(m^γ)` time
on *every* draw. Correctness and success probability require the separately
proved construction, decoder and verifier invariants. -/
theorem capped_runtime_strict_transfer (machine : BitRAM)
    (input : ℕ → List Bool) (tape : ℕ → ℕ → Bool) (cap : ℕ → ℕ)
    (θ γ : ℝ) (logPower : ℕ)
    (hcap : (fun n => (cap n : ℝ)) =O[atTop]
      (fun n => transferEnvelope θ logPower (n : ℝ)))
    (hconstruction : (3 : ℝ) / 2 < γ) (hsolver : θ < 2 * γ / 3) :
    (fun n => ((machine.run (input n) (tape n) (cap n)).instructions : ℝ))
      =o[atTop] (fun n => (n : ℝ) ^ γ) := by
  have henv := (transferEnvelope_littleO θ γ logPower hconstruction hsolver).comp_tendsto
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  exact ((bitRAM_capped_runtime_isBigO_cap machine input tape cap).trans hcap).trans_isLittleO henv

end Maxwell.Cost
