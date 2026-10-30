import Maxwell.Continuum.CalibrationLatticeDecay
import Maxwell.Continuum.CellSpatialCover

/-! Literal periodic-image separation for the one/two-well cell cover.
No geometric image-separation assumption is used in the final lemma. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.Calibration

open Bloch CellGauge

theorem imageRadius_attained (j : Bloch.Alias) :
    ∃ i : Fin 3, |(j i : ℝ)| = (imageRadius j : ℝ) := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup Finset.univ
    (Finset.univ_nonempty : (Finset.univ : Finset (Fin 3)).Nonempty)
    (fun i => (j i).natAbs)
  refine ⟨i, ?_⟩
  have he : (j i).natAbs = imageRadius j := hi.symm
  have hc := congrArg (fun n : ℕ => (n : ℝ)) he
  simpa only [Nat.cast_natAbs, Int.cast_abs] using hc

def twoWellCells (L : ℝ) (k : Bloch.Alias) : Finset Bloch.Alias :=
  (ballCells L) ∪ (wellCells L k)

theorem twoWellCells_card_le {L : ℝ} (hL : 1 ≤ L) (k : Bloch.Alias) :
    ((twoWellCells L k).card : ℝ) ≤ (2 : ℝ)^11*L^3 := by
  have hc := Finset.card_union_le (ballCells L) (wellCells L k)
  have hr : ((twoWellCells L k).card : ℝ) ≤
      ((ballCells L).card : ℝ)+((wellCells L k).card : ℝ) := by exact_mod_cast hc
  nlinarith [ballCells_card_le hL, wellCells_card_le hL k]

theorem ballCells_coordinate_bound {L : ℝ} (hL : 0 ≤ L) {a : Bloch.Alias}
    (ha : a ∈ ballCells L) (i : Fin 3) : |(a i : ℝ)| ≤ L+3 := by
  have hj := Finset.mem_Icc.mp (Fintype.mem_piFinset.mp ha i)
  have hc : |(a i : ℝ)| ≤ (ballCellRadius L : ℝ) :=
    abs_le.mpr ⟨by exact_mod_cast hj.1, by exact_mod_cast hj.2⟩
  have hceil := Nat.ceil_lt_add_one hL
  have hN : (ballCellRadius L : ℝ) ≤ L+3 := by
    simp only [ballCellRadius, Nat.cast_add, Nat.cast_ofNat]
    linarith
  exact hc.trans hN

theorem twoWellCells_coordinate_bound {L : ℝ} (hL : 0 ≤ L) (k : Bloch.Alias)
    {a : Bloch.Alias} (ha : a ∈ twoWellCells L k) (i : Fin 3) :
    |(a i : ℝ)| ≤ L+3+(imageRadius k : ℝ) := by
  rcases Finset.mem_union.mp ha with ha | ha
  · exact (ballCells_coordinate_bound hL ha i).trans (le_add_of_nonneg_right (Nat.cast_nonneg _))
  · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
    simp only [Pi.add_apply, Int.cast_add]
    exact (abs_add_le _ _).trans (add_le_add (ballCells_coordinate_bound hL hb i)
      (coordinate_le_imageRadius k i))

theorem periodic_image_distance {A : ℝ} (M : ℕ)
    (hM : 4*A ≤ (M : ℝ)) (a b j : Bloch.Alias)
    (ha : ∀ i, |(a i : ℝ)| ≤ A) (hb : ∀ i, |(b i : ℝ)| ≤ A) (hj : j ≠ 0) :
    (M : ℝ)*(imageRadius j : ℝ)/4 ≤ ‖integerVector ((b+M • j)-a)‖ := by
  obtain ⟨i, hi⟩ := imageRadius_attained j
  have hr : (1 : ℝ) ≤ imageRadius j := by exact_mod_cast Nat.succ_le_of_lt (imageRadius_pos hj)
  have hcoord : |(((b+M • j)-a) i : ℝ)| ≤ ‖integerVector ((b+M • j)-a)‖ := by
    simpa only [integerVector_apply, Real.norm_eq_abs] using
      PiLp.norm_apply_le (integerVector ((b+M • j)-a)) i
  have hd : |(b i : ℝ)-(a i : ℝ)| ≤ 2*A :=
    (abs_sub _ _).trans (by linarith [ha i, hb i])
  have he : |(M : ℝ)*(j i : ℝ)| ≤
      |(b i : ℝ)+(M : ℝ)*(j i : ℝ)-(a i : ℝ)|+|(b i : ℝ)-(a i : ℝ)| := by
    have ht := abs_sub ((b i : ℝ)+(M : ℝ)*(j i : ℝ)-(a i : ℝ)) ((b i : ℝ)-(a i : ℝ))
    convert ht using 1
    ring_nf
  rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg M), hi] at he
  have hcast : (((b+M • j)-a) i : ℝ) = (b i : ℝ)+(M : ℝ)*(j i : ℝ)-(a i : ℝ) := by
    change (((b i+M • (j i))-a i : ℤ) : ℝ) = _
    simp
  rw [hcast] at hcoord
  nlinarith [mul_le_mul_of_nonneg_left hr (Nat.cast_nonneg M)]

theorem twoWellCells_image_distance {L : ℝ} (hL : 1 ≤ L) (k : Bloch.Alias) (M : ℕ)
    (hM : 16*(L+(imageRadius k : ℝ)+1) ≤ (M : ℝ))
    {a b : Bloch.Alias} (ha : a ∈ twoWellCells L k) (hb : b ∈ twoWellCells L k)
    (j : Bloch.Alias) (hj : j ≠ 0) :
    (M : ℝ)*(imageRadius j : ℝ)/4 ≤ ‖integerVector ((b+M • j)-a)‖ := by
  have hL0 := le_trans zero_le_one hL
  apply periodic_image_distance (A := L+3+(imageRadius k : ℝ)) M
    (by nlinarith [show (0 : ℝ) ≤ imageRadius k from Nat.cast_nonneg _]) a b j
    (twoWellCells_coordinate_bound hL0 k ha) (twoWellCells_coordinate_bound hL0 k hb) hj

#print axioms twoWellCells_image_distance

end Maxwell.Continuum.Calibration
