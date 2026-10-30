import Maxwell.Continuum.ChebyshevWaveDegree
import Maxwell.Continuum.PeriodicSamplingTail

/-! Complete alias control for finite sampling of the angular plane waves. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.Profile

theorem wave_sampling_synthesis (k x : ℝ) :
    PeriodicSampling.synthesis (waveCoefficient k) x=waveAngular k (2*Real.pi*x) := by
  unfold PeriodicSampling.synthesis
  simp only [sampling_phase_mode, smul_eq_mul]
  exact (wave_hasSum k (2*Real.pi*x)).tsum_eq

theorem waveCoefficient_tail (k : ℝ) (D : ℕ) :
    PeriodicSampling.tail (waveCoefficient k) (D : ℤ) ≤
      16*Real.exp (4*|k|)*(1/2 : ℝ)^(D/2) := by
  let f : ℤ → ℝ := fun n => if (D : ℤ)≤|n| then ‖waveCoefficient k n‖ else 0
  have hs : Summable f := PeriodicSampling.tail_summable _ (waveCoefficient_summable_norm k) _
  have hi : Function.Injective (fun n : ℕ => (n : ℤ)) := Nat.cast_injective
  have hp := hs.comp_injective hi
  have hm := hs.comp_injective (neg_injective.comp hi)
  have ht : Summable (fun n : ℕ => if D≤n then (1/2 : ℝ)^(n/2) else 0) := by
    apply Summable.of_nonneg_of_le (fun n => by split_ifs <;> positivity) _ half_geometric_summable
    intro n
    split_ifs
    · exact le_rfl
    · positivity
  have hbound (n : ℕ) : f n ≤ Real.exp (4*|k|)*(if D≤n then (1/2 : ℝ)^(n/2) else 0) ∧
      f (-(n : ℤ)) ≤ Real.exp (4*|k|)*(if D≤n then (1/2 : ℝ)^(n/2) else 0) := by
    have hpn := waveCoefficient_decay k (n : ℤ)
    have hmn := waveCoefficient_decay k (-(n : ℤ))
    simp only [Int.natAbs_natCast, Int.natAbs_neg] at hpn hmn
    simp only [f, abs_neg, Int.abs_natCast, Int.ofNat_le]
    split_ifs
    · exact ⟨hpn,hmn⟩
    · simp
  have hplus := hp.tsum_le_tsum (fun n => (hbound n).1) (ht.mul_left _)
  have hminus := hm.tsum_le_tsum (fun n => (hbound n).2) (ht.mul_left _)
  rw [tsum_mul_left] at hplus hminus
  have hf0 : 0≤f 0 := by dsimp [f]; split_ifs <;> positivity
  change (∑' n : ℤ, f n) ≤ _
  rw [hp.tsum_of_nat_of_neg hm]
  have ht := mul_le_mul_of_nonneg_left (half_geometric_tail D) (Real.exp_nonneg (4*|k|))
  nlinarith only [hplus,hminus,hf0,ht]

theorem wave_sample_precision (grid D K P : ℕ) [NeZero grid] {k : ℝ} (hk : |k|≤K)
    (n : ℤ) (hn : |n|≤(D : ℤ)) (hgrid : waveDegree K P+D≤grid) :
    ‖PeriodicSampling.coefficient grid
      (fun j => waveAngular k (2*Real.pi*((j.val : ℝ)/grid))) (n : ZMod grid)-waveCoefficient k n‖ ≤
      (1/2 : ℝ)^(P+100) := by
  have hs := PeriodicSampling.coefficient_samples_error_window grid
    (waveCoefficient k) (waveCoefficient_summable_norm k) D n hn
  simp_rw [wave_sampling_synthesis] at hs
  have hm := PeriodicSampling.tail_mono (waveCoefficient k) (waveCoefficient_summable_norm k)
    (show (waveDegree K P : ℤ)≤(grid : ℤ)-D by omega)
  exact hs.trans (hm.trans ((waveCoefficient_tail k (waveDegree K P)).trans (waveDegree_precision K P hk)))

#print axioms wave_sample_precision

end Maxwell.Continuum.Profile
