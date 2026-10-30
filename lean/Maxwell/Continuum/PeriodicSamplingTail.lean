import Maxwell.Continuum.PeriodicSampling

/-! The exact alias formula gives a certified sampling error controlled
by the full Fourier tail beyond `N-|k|`. -/

noncomputable section

namespace Maxwell.Continuum.PeriodicSampling

open scoped Classical

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable (N : ℕ) [NeZero N]

omit [NeZero N] in
theorem alias_radius {n k : ℤ} (hne : n ≠ k) (hn : (n : ZMod N) = (k : ZMod N)) :
    (N : ℤ)-|k| ≤ |n| := by
  have hd : (N : ℤ) ∣ n-k := (ZMod.intCast_zmod_eq_zero_iff_dvd (n-k) N).mp (by
    push_cast
    rw [hn,sub_self])
  have hb := Int.natAbs_le_of_dvd_ne_zero hd (sub_ne_zero.mpr hne)
  have hcast := Int.ofNat_le.mpr hb
  have hb' : (N : ℤ) ≤ |n-k| := by
    simpa only [Int.natAbs_natCast,Int.natCast_natAbs] using hcast
  have ht := abs_sub n k
  omega

def tail (c : ℤ → E) (R : ℤ) : ℝ := ∑' n : ℤ, if R ≤ |n| then ‖c n‖ else 0

omit [NormedSpace ℂ E] [CompleteSpace E] in
theorem tail_summable (c : ℤ → E) (hc : Summable (fun n => ‖c n‖)) (R : ℤ) :
    Summable (fun n : ℤ => if R ≤ |n| then ‖c n‖ else 0) := by
  apply Summable.of_nonneg_of_le _ _ hc
  · intro n
    split_ifs <;> positivity
  · intro n
    split_ifs <;> simp

def aliasRemainder (c : ℤ → E) (k n : ℤ) : E :=
  if n = k then 0 else if (n : ZMod N) = (k : ZMod N) then c n else 0

omit [NormedSpace ℂ E] [CompleteSpace E] [NeZero N] in
theorem aliasRemainder_norm_le (c : ℤ → E) (k n : ℤ) :
    ‖aliasRemainder N c k n‖ ≤ ‖c n‖ := by
  unfold aliasRemainder
  split_ifs <;> simp

omit [NormedSpace ℂ E] [CompleteSpace E] [NeZero N] in
theorem aliasRemainder_summable_norm (c : ℤ → E) (hc : Summable (fun n => ‖c n‖)) (k : ℤ) :
    Summable (fun n => ‖aliasRemainder N c k n‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (aliasRemainder_norm_le N c k) hc

theorem coefficient_samples_sub (c : ℤ → E) (hc : Summable (fun n => ‖c n‖)) (k : ℤ) :
    coefficient N (fun j => synthesis c ((j.val : ℝ)/N)) (k : ZMod N)-c k =
      ∑' n : ℤ, aliasRemainder N c k n := by
  rw [coefficient_samples N c hc k]
  have hs : Summable (fun n : ℤ => if (n : ZMod N) = (k : ZMod N) then c n else 0) := by
    apply Summable.of_norm_bounded hc
    intro n
    split_ifs <;> simp
  rw [hs.tsum_eq_add_tsum_ite k]
  simp only [↓reduceIte]
  change (c k+∑' n : ℤ,aliasRemainder N c k n)-c k = _
  abel

theorem coefficient_samples_error (c : ℤ → E) (hc : Summable (fun n => ‖c n‖)) (k : ℤ) :
    ‖coefficient N (fun j => synthesis c ((j.val : ℝ)/N)) (k : ZMod N)-c k‖ ≤
      tail c ((N : ℤ)-|k|) := by
  rw [coefficient_samples_sub N c hc k]
  apply (norm_tsum_le_tsum_norm (aliasRemainder_summable_norm N c hc k)).trans
  apply Summable.tsum_le_tsum _ (aliasRemainder_summable_norm N c hc k)
    (tail_summable c hc _)
  intro n
  by_cases hnk : n = k
  · simp only [aliasRemainder,hnk,↓reduceIte,norm_zero]
    split_ifs <;> positivity
  · by_cases hmod : (n : ZMod N) = (k : ZMod N)
    · simp only [aliasRemainder,hnk,hmod,alias_radius N hnk hmod,↓reduceIte]
      exact le_rfl
    · simp only [aliasRemainder,hnk,hmod,↓reduceIte,norm_zero]
      split_ifs <;> positivity

omit [NormedSpace ℂ E] [CompleteSpace E] in
theorem tail_mono (c : ℤ → E) (hc : Summable (fun n => ‖c n‖)) {R S : ℤ} (hRS : R ≤ S) :
    tail c S ≤ tail c R := by
  apply Summable.tsum_le_tsum _ (tail_summable c hc S) (tail_summable c hc R)
  intro n
  by_cases hS : S ≤ |n|
  · simp only [hS,hRS.trans hS,↓reduceIte]
    exact le_rfl
  · simp only [hS,↓reduceIte]
    split_ifs <;> positivity

theorem coefficient_samples_error_window (c : ℤ → E) (hc : Summable (fun n => ‖c n‖))
    (K : ℕ) (k : ℤ) (hk : |k| ≤ (K : ℤ)) :
    ‖coefficient N (fun j => synthesis c ((j.val : ℝ)/N)) (k : ZMod N)-c k‖ ≤
      tail c ((N : ℤ)-K) :=
  (coefficient_samples_error N c hc k).trans (tail_mono c hc (by omega))

#print axioms coefficient_samples_error
#print axioms coefficient_samples_error_window

end Maxwell.Continuum.PeriodicSampling
