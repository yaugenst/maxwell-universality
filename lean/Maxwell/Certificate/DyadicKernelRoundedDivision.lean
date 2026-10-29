import Maxwell.Certificate.DyadicKernelRoundedSound

namespace Maxwell.Certificate.DyadicKernel

private theorem centerRadius_lower (lo hi : ℤ) :
    (centerRadius lo hi).1 - ((centerRadius lo hi).2 : ℤ) ≤ lo := by
  have h := Nat.le_max_left ((lo+hi)/2-lo).natAbs (hi-(lo+hi)/2).natAbs
  have hh : |(lo+hi)/2-lo| ≤ ((max ((lo+hi)/2-lo).natAbs (hi-(lo+hi)/2).natAbs : ℕ):ℤ) := by
    simpa only [Int.natCast_natAbs] using (Int.ofNat_le.mpr h)
  dsimp [centerRadius]
  linarith [le_abs_self ((lo+hi)/2-lo)]

private theorem centerRadius_upper (lo hi : ℤ) :
    hi ≤ (centerRadius lo hi).1 + ((centerRadius lo hi).2 : ℤ) := by
  have h := Nat.le_max_right ((lo+hi)/2-lo).natAbs (hi-(lo+hi)/2).natAbs
  have hh : |hi-(lo+hi)/2| ≤ ((max ((lo+hi)/2-lo).natAbs (hi-(lo+hi)/2).natAbs : ℕ):ℤ) := by
    simpa only [Int.natCast_natAbs] using (Int.ofNat_le.mpr h)
  dsimp [centerRadius]
  linarith [le_abs_self (hi-(lo+hi)/2)]

private theorem ceil_mul (x d : ℤ) (hd : 0 < d) : x ≤ (-((-x)/d))*d := by
  have h := Int.ediv_mul_le (-x) (ne_of_gt hd)
  nlinarith

private theorem channel_round_checked (p : ℕ) (a b : ℤ) (ar br R : ℕ)
    (hb : 0 < b-(br:ℤ))
    (hR : (centerRadius (lowerQuotient p a ar b br) (upperQuotient p a ar b br)).2 ≤ R) :
    channelDivCheck p a ar b br
      (centerRadius (lowerQuotient p a ar b br) (upperQuotient p a ar b br)).1 R = true := by
  let lo := lowerQuotient p a ar b br
  let hi := upperQuotient p a ar b br
  let c := (centerRadius lo hi).1
  have hr : ((centerRadius lo hi).2:ℤ) ≤ (R:ℤ) := by exact_mod_cast hR
  have hc : c-(R:ℤ) ≤ lo := by
    have h := centerRadius_lower lo hi
    dsimp [c]
    linarith
  have hd : hi ≤ c+(R:ℤ) := by
    have h := centerRadius_upper lo hi
    dsimp [c]
    linarith
  have hb' : 0 < b+(br:ℤ) := by omega
  apply decide_eq_true
  change (c-R)*(b-br) ≤ (a-ar)*(2:ℤ)^p ∧
      (c-R)*(b+br) ≤ (a-ar)*(2:ℤ)^p ∧
      (a+ar)*(2:ℤ)^p ≤ (c+R)*(b-br) ∧
      (a+ar)*(2:ℤ)^p ≤ (c+R)*(b+br)
  refine ⟨?_,?_,?_,?_⟩
  · exact (mul_le_mul_of_nonneg_right (hc.trans (min_le_left _ _)) hb.le).trans
      (Int.ediv_mul_le _ (ne_of_gt hb))
  · exact (mul_le_mul_of_nonneg_right (hc.trans (min_le_right _ _)) hb'.le).trans
      (Int.ediv_mul_le _ (ne_of_gt hb'))
  · have h := ceil_mul ((a+ar)*(2:ℤ)^p) (b-br) hb
    have hu := mul_le_mul_of_nonneg_right ((le_max_left _ _).trans hd) hb.le
    change -((-(a+ar)*(2:ℤ)^p)/(b-br))*(b-br) ≤ (c+R)*(b-br) at hu
    apply h.trans
    simpa only [neg_mul] using hu
  · have h := ceil_mul ((a+ar)*(2:ℤ)^p) (b+br) hb'
    have hu := mul_le_mul_of_nonneg_right ((le_max_right _ _).trans hd) hb'.le
    change -((-(a+ar)*(2:ℤ)^p)/(b+br))*(b+br) ≤ (c+R)*(b+br) at hu
    apply h.trans
    simpa only [neg_mul] using hu

theorem divRound_checked {p : ℕ} {a b c : Rectangle}
    (h : divRound p a b = some c) : divCheck p a b c = true := by
  rcases a with ⟨ar,ai,ae⟩
  rcases b with ⟨br,bi,be⟩
  simp only [divRound] at h
  split_ifs at h with hp
  · cases Option.some.inj h
    apply Bool.and_eq_true_iff.mpr
    constructor
    · apply Bool.and_eq_true_iff.mpr
      exact ⟨decide_eq_true hp, channel_round_checked _ _ _ _ _ _ hp (Nat.le_max_left _ _)⟩
    · exact channel_round_checked _ _ _ _ _ _ hp (Nat.le_max_right _ _)

theorem divRound_contains {p : ℕ} {a b c : Rectangle} {z : ℂ} {x : ℝ}
    (h : divRound p a b = some c) (ha : a.toDyadic.Contains p z)
    (hb : b.toDyadic.Contains p (x:ℂ)) : c.toDyadic.Contains p (z/(x:ℂ)) := by
  apply DyadicRectangle.divCheck_sound _ ha hb
  rw [← divCheck_eq]
  exact divRound_checked h

end Maxwell.Certificate.DyadicKernel
