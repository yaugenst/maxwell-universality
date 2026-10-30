import Maxwell.Continuum.CalibrationSupercellWellCompression
import Maxwell.Continuum.WellInteractionBound

/-! The same literal supercell inverse approximates the translated
two-well interaction, with a global physical operator-norm estimate. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace Maxwell.Continuum.Calibration.Supercell

open FreeFiber CellGauge CellBandFourier PeriodicSampling Auxiliary Bloch MasterConstants EffectiveMass

variable (M : ℕ) [NeZero M]

attribute [local irreducible] physicalOperator actualGridInverse Qh periodizedCompression Auxiliary.resolvent

omit [NeZero M] in
theorem rectangular_periodization_error {L z σ : ℝ} (hL : Ls≤L)
    (D : Auxiliary.Calibration L⁻¹ z) (hσ0 : 0≤σ) (hσ : σ≤(L⁻¹)^4/64)
    (k : Bloch.Alias) (hM : 16*(L+(imageRadius k : ℝ)+1)≤(M : ℝ))
    (s t : Finset Bloch.Alias) (hs : s⊆twoWellCells L k) (ht : t⊆twoWellCells L k) :
    ‖periodizedCompression D hσ0 hσ M s t-
      (familyProjection s).comp ((Auxiliary.resolvent D hσ0 hσ).comp (familyProjection t))‖ ≤
      Cs^2*L^10*Real.exp (-(cs/8)*Real.sqrt (M/L)) := by
  have hL1 := length_ge_one hL
  have hM0 : L≤(M : ℝ) := by nlinarith [show (0 : ℝ) ≤ imageRadius k from Nat.cast_nonneg _]
  have hd := fun a ha b hb j hj => twoWellCells_image_distance hL1 k M hM
    (a := a) (b := b) (hs ha) (ht hb) j hj
  have hc := twoWellCells_card_le hL1 k
  have hsc : (s.card : ℝ)≤(2 : ℝ)^11*L^3 :=
    (show (s.card : ℝ)≤(twoWellCells L k).card by exact_mod_cast Finset.card_le_card hs).trans hc
  have htc : (t.card : ℝ)≤(2 : ℝ)^11*L^3 :=
    (show (t.card : ℝ)≤(twoWellCells L k).card by exact_mod_cast Finset.card_le_card ht).trans hc
  apply (periodizedCompression_error_count hL D hσ0 hσ M hM0 s t hd).trans
  have he : Real.exp (-(cs/4)*Real.sqrt ((M : ℝ)/L)) ≤
      Real.exp (-(cs/8)*Real.sqrt ((M : ℝ)/L)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg cs_pos.le (Real.sqrt_nonneg ((M : ℝ)/L))]
  calc
    _ ≤ ((2 : ℝ)^11*L^3)*((2 : ℝ)^11*L^3)*
        ((Cs^2/(2 : ℝ)^32)*L^4*Real.exp (-(cs/4)*Real.sqrt ((M : ℝ)/L))) := by gcongr
    _ = (1/(2 : ℝ)^10)*(Cs^2*L^10)*Real.exp (-(cs/4)*Real.sqrt ((M : ℝ)/L)) := by ring
    _ ≤ 1*(Cs^2*L^10)*Real.exp (-(cs/8)*Real.sqrt ((M : ℝ)/L)) := by
      gcongr
      norm_num
    _ = _ := by ring

def physicalWellInteraction {L z σ : ℝ} (_D : Auxiliary.Calibration L⁻¹ z)
    (_hσ0 : 0≤σ) (_hσ : σ≤(L⁻¹)^4/64) (k : Bloch.Alias) : FieldL2 →L[ℂ] FieldL2 :=
  (Qh L⁻¹).comp
    ((physicalOperator M (fun j => actualGridInverse z σ (fun i => centeredGrid M (j i)))).comp
      ((translationOperator (-latticeShift k)).comp (Qh L⁻¹)))

theorem physicalWellInteraction_factor {L z σ : ℝ} (hL : Ls≤L)
    (D : Auxiliary.Calibration L⁻¹ z) (hσ0 : 0≤σ) (hσ : σ≤(L⁻¹)^4/64)
    (hEven : Even M) (k : Bloch.Alias)
    (hM : 16*(L+(imageRadius k : ℝ)+1)≤(M : ℝ)) :
    physicalWellInteraction M D hσ0 hσ k=
      (Qh L⁻¹).comp ((periodizedCompression D hσ0 hσ M (ballCells L) (wellCells L k)).comp
        ((translationOperator (-latticeShift k)).comp (Qh L⁻¹))) := by
  have hL1 := length_ge_one hL
  have hM0 : L≤(M : ℝ) := by nlinarith [show (0 : ℝ) ≤ imageRadius k from Nat.cast_nonneg _]
  have hs : ballCells L⊆twoWellCells L k := Finset.subset_union_left
  have ht : wellCells L k⊆twoWellCells L k := Finset.subset_union_right
  have hc := physicalOperator_compression M hL D hσ0 hσ hM0 hEven (ballCells L) (wellCells L k)
    (fun _ ha => twoWellCells_representative M hL1 k hM (hs ha))
    (fun _ hb => twoWellCells_representative M hL1 k hM (ht hb))
    (fun _ ha _ hb j hj => twoWellCells_image_distance hL1 k M hM (hs ha) (ht hb) j hj)
  rw [← hc]
  apply ContinuousLinearMap.ext
  intro f
  change Qh L⁻¹ (physicalOperator M _ (fieldTranslation (-latticeShift k) (Qh L⁻¹ f)))=
    Qh L⁻¹ (familyProjection (ballCells L) (physicalOperator M _
      (familyProjection (wellCells L k) (fieldTranslation (-latticeShift k) (Qh L⁻¹ f)))))
  rw [familyProjection_translatedQh (length_pos hL)]
  exact (congrArg (fun T : FieldL2 →L[ℂ] FieldL2 =>
    T (physicalOperator M _ (fieldTranslation (-latticeShift k) (Qh L⁻¹ f))))
      (Qh_familyProjection (length_pos hL))).symm

theorem well_sandwich_norm {L : ℝ} (T : FieldL2 →L[ℂ] FieldL2) (k : Bloch.Alias) :
    ‖(Qh L⁻¹).comp (T.comp ((translationOperator (-latticeShift k)).comp (Qh L⁻¹)))‖≤‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro f
  change ‖Qh L⁻¹ (T (fieldTranslation (-latticeShift k) (Qh L⁻¹ f)))‖≤‖T‖*‖f‖
  calc
    _ ≤ ‖T (fieldTranslation (-latticeShift k) (Qh L⁻¹ f))‖ := by
      simpa only [one_mul] using (Qh L⁻¹).le_of_opNorm_le (Qh_norm_le L⁻¹) _
    _ ≤ ‖T‖*‖fieldTranslation (-latticeShift k) (Qh L⁻¹ f)‖ := T.le_opNorm _
    _ ≤ ‖T‖*‖f‖ := by
      rw [LinearIsometryEquiv.norm_map]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      simpa only [one_mul] using (Qh L⁻¹).le_of_opNorm_le (Qh_norm_le L⁻¹) f

theorem physicalWellInteraction_error {L z σ : ℝ} (hL : Ls≤L)
    (D : Auxiliary.Calibration L⁻¹ z) (hσ0 : 0≤σ) (hσ : σ≤(L⁻¹)^4/64)
    (hEven : Even M) (k : Bloch.Alias)
    (hM : 16*(L+(imageRadius k : ℝ)+1)≤(M : ℝ)) :
    ‖physicalWellInteraction M D hσ0 hσ k-wellInteraction D hσ0 hσ k‖≤
      Cs^2*L^10*Real.exp (-(cs/8)*Real.sqrt (M/L)) := by
  rw [physicalWellInteraction_factor M hL D hσ0 hσ hEven k hM,
    wellInteraction_factor (length_pos hL) D hσ0 hσ k,
    ← ContinuousLinearMap.comp_sub,← ContinuousLinearMap.sub_comp]
  exact (well_sandwich_norm _ k).trans
    (rectangular_periodization_error M hL D hσ0 hσ k hM _ _
      Finset.subset_union_left Finset.subset_union_right)

theorem physicalWellInteraction_requested_error {L z σ : ℝ} (hL : Ls≤L)
    (D : Auxiliary.Calibration L⁻¹ z) (hσ0 : 0≤σ) (hσ : σ≤(L⁻¹)^4/64)
    (hEven : Even M) (k : Bloch.Alias) (N ell : ℕ)
    (hM : 16*(L+(imageRadius k : ℝ)+1)≤(M : ℝ))
    (hlog : L≤(2 : ℝ)^ell) (hsize : Cs^4*L*((N : ℝ)+(ell : ℝ)+2)^2≤(M : ℝ)) :
    ‖physicalWellInteraction M D hσ0 hσ k-wellInteraction D hσ0 hσ k‖≤(1/2 : ℝ)^(N+20) :=
  (physicalWellInteraction_error M hL D hσ0 hσ hEven k hM).trans
    (periodization_error_budget (length_pos hL) N ell hlog hsize)

#print axioms physicalWellInteraction_requested_error

end Maxwell.Continuum.Calibration.Supercell
