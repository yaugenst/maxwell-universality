import Maxwell.Continuum.ProfileFourierSeries
import Maxwell.Continuum.ProfileDegree
import Maxwell.Continuum.PeriodicSamplingTail

/-! Complete alias-tail estimates for sampling the actual flat angular profile. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.Profile

theorem weighted_exp64_tail_summable (D : ℕ) :
    Summable (fun j : ℕ => if D ≤ j then
      (1+(j : ℝ)^2)*Real.exp (-Real.sqrt j/64) else 0) := by
  apply Summable.of_nonneg_of_le (fun j => by split_ifs <;> positivity) _ weighted_exp_summable
  intro j
  split_ifs
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Real.exp_le_exp.mpr (by linarith [Real.sqrt_nonneg (j : ℝ)])
  · positivity

theorem angularCoefficient_tail (D : ℕ) :
    PeriodicSampling.tail (angularCoefficient 0) (D : ℤ) ≤
      (2 : ℝ)^87*Real.exp (-Real.sqrt D/128) := by
  let f : ℤ → ℝ := fun n => if (D : ℤ) ≤ |n| then ‖angularCoefficient 0 n‖ else 0
  have hs : Summable f := PeriodicSampling.tail_summable _ angularCoefficient_summable_norm _
  have hi : Function.Injective (fun n : ℕ => (n : ℤ)) := Nat.cast_injective
  have hp := hs.comp_injective hi
  have hm := hs.comp_injective (neg_injective.comp hi)
  have hbound (n : ℕ) : f n ≤ 24*(if D ≤ n then
      (1+(n : ℝ)^2)*Real.exp (-Real.sqrt n/64) else 0) ∧
      f (-(n : ℤ)) ≤ 24*(if D ≤ n then
      (1+(n : ℝ)^2)*Real.exp (-Real.sqrt n/64) else 0) := by
    have hpn := angularCoefficient_decay (n : ℤ)
    have hmn := angularCoefficient_decay (-(n : ℤ))
    simp only [Int.cast_natCast, Int.cast_neg, abs_neg,
      abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)] at hpn hmn
    simp only [f, abs_neg, Int.abs_natCast, Int.ofNat_le]
    split_ifs with hDn
    · have he : 0 ≤ Real.exp (-Real.sqrt (n : ℝ)/64) := Real.exp_nonneg _
      constructor <;> nlinarith only [hpn, hmn, mul_nonneg (sq_nonneg (n : ℝ)) he]
    · simp
  have hsum := (weighted_exp64_tail_summable D).mul_left 24
  have hplus := hp.tsum_le_tsum (fun n => (hbound n).1) hsum
  have hminus := hm.tsum_le_tsum (fun n => (hbound n).2) hsum
  rw [tsum_mul_left] at hplus hminus
  have hf0 : 0 ≤ f 0 := by dsimp [f]; split_ifs <;> positivity
  change (∑' n : ℤ, f n) ≤ _
  rw [hp.tsum_of_nat_of_neg hm]
  have ht := weighted_exp_tail D
  have he := Real.exp_pos (-Real.sqrt (D : ℝ)/128)
  nlinarith only [hplus, hminus, hf0, ht, he]

theorem angularCoefficient_tail_precision (N : ℕ) :
    PeriodicSampling.tail (angularCoefficient 0) (profileDegree N : ℤ) ≤
      (1/2 : ℝ)^(N+100) := by
  apply (angularCoefficient_tail (profileDegree N)).trans
  apply le_trans _ (profileDegree_precision N)
  gcongr <;> norm_num

theorem angular_sample_error (grid D S : ℕ) [NeZero grid] (k : ℤ)
    (hk : |k| ≤ (D : ℤ)) (hgrid : S+D ≤ grid) :
    ‖PeriodicSampling.coefficient grid
      (fun j => ((angular (2*Real.pi*((j.val : ℝ)/grid)) : ℝ) : ℂ)) (k : ZMod grid) -
      angularCoefficient 0 k‖ ≤ (2 : ℝ)^87*Real.exp (-Real.sqrt S/128) := by
  have h := PeriodicSampling.coefficient_samples_error_window grid
    (angularCoefficient 0) angularCoefficient_summable_norm D k hk
  simp_rw [angular_sampling_synthesis] at h
  exact h.trans ((PeriodicSampling.tail_mono _ angularCoefficient_summable_norm
    (show (S : ℤ) ≤ (grid : ℤ)-D by omega)).trans (angularCoefficient_tail S))

theorem angular_sample_precision (grid D N : ℕ) [NeZero grid] (k : ℤ)
    (hk : |k| ≤ (D : ℤ)) (hgrid : profileDegree N+D ≤ grid) :
    ‖PeriodicSampling.coefficient grid
      (fun j => ((angular (2*Real.pi*((j.val : ℝ)/grid)) : ℝ) : ℂ)) (k : ZMod grid) -
      angularCoefficient 0 k‖ ≤ (1/2 : ℝ)^(N+100) := by
  apply (angular_sample_error grid D (profileDegree N) k hk hgrid).trans
  apply le_trans _ (profileDegree_precision N)
  gcongr <;> norm_num

#print axioms angularCoefficient_tail
#print axioms angular_sample_precision

end Maxwell.Continuum.Profile
