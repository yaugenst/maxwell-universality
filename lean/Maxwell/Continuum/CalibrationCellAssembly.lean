import Maxwell.Continuum.CalibrationPeriodizedCell

/-! The periodic cell maps are assembled on the same physical L² space
as the original one/two-well resolvent compression. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 4096

namespace Maxwell.Continuum.Calibration

open Auxiliary Bloch CellGauge MasterConstants

def liftCellBlock (a b : Bloch.Alias) (T : CellMap) : FieldL2 →L[ℂ] FieldL2 :=
  (1/8 : ℂ) • (embedLatticeCell a).comp (T.comp (restrictLatticeCell b))

theorem liftCellBlock_sub (a b : Bloch.Alias) (T S : CellMap) :
    liftCellBlock a b (T-S) = liftCellBlock a b T-liftCellBlock a b S := by
  apply ContinuousLinearMap.ext
  intro f
  simp [liftCellBlock, smul_sub]

theorem liftCellBlock_norm_le (a b : Bloch.Alias) (T : CellMap) : ‖liftCellBlock a b T‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro f
  change ‖(1/8 : ℂ) • embedLatticeCell a (T (restrictLatticeCell b f))‖ ≤ _
  rw [norm_smul]
  norm_num only [norm_div, norm_one, Complex.norm_ofNat]
  have he := embedLatticeCell_norm_le a (T (restrictLatticeCell b f))
  have ht := (T.le_opNorm (restrictLatticeCell b f)).trans
    (mul_le_mul_of_nonneg_left (restrictLatticeCell_norm_le b f) (norm_nonneg T))
  nlinarith [mul_nonneg (norm_nonneg T) (norm_nonneg f)]

theorem liftCellBlock_resolvent {L z σ : ℝ} (D : Auxiliary.Calibration L⁻¹ z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ (L⁻¹)^4/64) (a b : Bloch.Alias) :
    liftCellBlock a b (resolventCellBlock D hσ0 hσ a b) =
      (cellProjection a).comp ((resolvent D hσ0 hσ).comp (cellProjection b)) :=
  (spatialBlock_factor (resolvent D hσ0 hσ) a b).symm

def periodizedCompression {L z σ : ℝ} (D : Auxiliary.Calibration L⁻¹ z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ (L⁻¹)^4/64) (M : ℕ) (s t : Finset Bloch.Alias) :
    FieldL2 →L[ℂ] FieldL2 :=
  ∑ a ∈ s, ∑ b ∈ t, liftCellBlock a b (periodizedCellBlock D hσ0 hσ M a b)

theorem compression_eq_sum {L z σ : ℝ} (D : Auxiliary.Calibration L⁻¹ z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ (L⁻¹)^4/64) (s t : Finset Bloch.Alias) :
    (familyProjection s).comp ((resolvent D hσ0 hσ).comp (familyProjection t)) =
      ∑ a ∈ s, ∑ b ∈ t, liftCellBlock a b (resolventCellBlock D hσ0 hσ a b) := by
  simp_rw [liftCellBlock_resolvent]
  apply ContinuousLinearMap.ext
  intro f
  simp only [ContinuousLinearMap.comp_apply, familyProjection_apply, map_sum, sum_apply]
  rw [Finset.sum_comm]

theorem periodizedCompression_error_count {L z σ : ℝ} (hL : Ls ≤ L)
    (D : Auxiliary.Calibration L⁻¹ z) (hσ0 : 0 ≤ σ) (hσ : σ ≤ (L⁻¹)^4/64)
    (M : ℕ) (hM : L ≤ (M : ℝ)) (s t : Finset Bloch.Alias)
    (hd : ∀ a ∈ s, ∀ b ∈ t, ∀ j : Bloch.Alias, j ≠ 0 →
      (M : ℝ)*(imageRadius j : ℝ)/4 ≤ ‖integerVector ((b+M • j)-a)‖) :
    ‖periodizedCompression D hσ0 hσ M s t-
      (familyProjection s).comp ((resolvent D hσ0 hσ).comp (familyProjection t))‖ ≤
      (s.card : ℝ)*(t.card : ℝ)*
        ((Cs^2/(2 : ℝ)^32)*L^4*Real.exp (-(cs/4)*Real.sqrt (M/L))) := by
  rw [compression_eq_sum]
  unfold periodizedCompression
  rw [← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib, ← liftCellBlock_sub]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ a ∈ s, ∑ b ∈ t,
        ‖liftCellBlock a b (periodizedCellBlock D hσ0 hσ M a b-resolventCellBlock D hσ0 hσ a b)‖ :=
      Finset.sum_le_sum (fun a _ => norm_sum_le _ _)
    _ ≤ ∑ _a ∈ s, ∑ _b ∈ t,
        ((Cs^2/(2 : ℝ)^32)*L^4*Real.exp (-(cs/4)*Real.sqrt (M/L))) := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro b hb
      exact (liftCellBlock_norm_le a b _).trans
        (periodizedCellBlock_error hL D hσ0 hσ M hM a b (hd a ha b hb))
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

theorem twoWell_periodization_error {L z σ : ℝ} (hL : Ls ≤ L)
    (D : Auxiliary.Calibration L⁻¹ z) (hσ0 : 0 ≤ σ) (hσ : σ ≤ (L⁻¹)^4/64)
    (k : Bloch.Alias) (M : ℕ) (hM : 16*(L+(imageRadius k : ℝ)+1) ≤ (M : ℝ)) :
    ‖periodizedCompression D hσ0 hσ M (twoWellCells L k) (twoWellCells L k)-
      (familyProjection (twoWellCells L k)).comp
        ((resolvent D hσ0 hσ).comp (familyProjection (twoWellCells L k)))‖ ≤
      Cs^2*L^10*Real.exp (-(cs/8)*Real.sqrt (M/L)) := by
  have hL1 := length_ge_one hL
  have hM0 : L ≤ (M : ℝ) := by nlinarith [show (0 : ℝ) ≤ imageRadius k from Nat.cast_nonneg _]
  have hd := fun a ha b hb j hj => twoWellCells_image_distance hL1 k M hM
    (a := a) (b := b) ha hb j hj
  have hc := twoWellCells_card_le hL1 k
  apply (periodizedCompression_error_count hL D hσ0 hσ M hM0
    (twoWellCells L k) (twoWellCells L k) hd).trans
  have he : Real.exp (-(cs/4)*Real.sqrt ((M : ℝ)/L)) ≤
      Real.exp (-(cs/8)*Real.sqrt ((M : ℝ)/L)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg cs_pos.le (Real.sqrt_nonneg ((M : ℝ)/L))]
  calc
    _ ≤ ((2 : ℝ)^11*L^3)*((2 : ℝ)^11*L^3)*
        ((Cs^2/(2 : ℝ)^32)*L^4*Real.exp (-(cs/4)*Real.sqrt ((M : ℝ)/L))) := by
      gcongr
    _ = (1/(2 : ℝ)^10)*(Cs^2*L^10)*Real.exp (-(cs/4)*Real.sqrt ((M : ℝ)/L)) := by ring
    _ ≤ 1*(Cs^2*L^10)*Real.exp (-(cs/8)*Real.sqrt ((M : ℝ)/L)) := by
      gcongr
      norm_num
    _ = _ := by ring

#print axioms twoWell_periodization_error

end Maxwell.Continuum.Calibration
