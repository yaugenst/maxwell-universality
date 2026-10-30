import Maxwell.Continuum.ParameterGeometry
import Maxwell.Continuum.BoxModesCutoffSpectrum
import Maxwell.Continuum.BoxCellGeometry
import Maxwell.Composition.SelectedVolumeBounds

/-! Literal box volume and well count for the selected continuum source instance. -/

noncomputable section
namespace Maxwell.Continuum.Parameters
open Maxwell.Composition MasterConstants
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1000000

/-- Fixed coefficient for each actual padded half-side. -/
def sourceSideCoefficient (p : Source.Parameters) : ℕ :=
  let M := sourceMagnitude p
  2*2^(6+45*M)*2^(9*M)*(2^54*129)+2^(6+45*M)+2^(6+56*M)+8

private theorem padded_side_bound {L d b s ℓ A D B : ℕ}
    (hℓ : 0 < ℓ) (hs : 0 < s) (hL : L ≤ A*ℓ^6)
    (hd : d ≤ D*ℓ) (hb : b ≤ B*ℓ^7) :
    2*L*d*(2^54*129*s)+L+b+8 ≤
      (2*A*D*(2^54*129)+A+B+8)*s*ℓ^7 := by
  have hl7 : 1 ≤ ℓ^7 := one_le_pow₀ (by omega : 1 ≤ ℓ)
  have hl67 : ℓ^6 ≤ ℓ^7 := Nat.pow_le_pow_right hℓ (by omega)
  have hmain := Nat.mul_le_mul hL hd
  have hmain' : 2*L*d*(2^54*129*s) ≤ 2*A*D*(2^54*129)*s*ℓ^7 := by
    calc
      _ = (L*d)*(2*(2^54*129*s)) := by ring
      _ ≤ ((A*ℓ^6)*(D*ℓ))*(2*(2^54*129*s)) := Nat.mul_le_mul_right _ hmain
      _ = _ := by ring
  have hL' : L ≤ A*s*ℓ^7 :=
    (hL.trans (Nat.mul_le_mul_left A hl67)).trans (by
      calc
        A*ℓ^7 ≤ (A*ℓ^7)*s := Nat.le_mul_of_pos_right _ hs
        _ = _ := by ring)
  have hb' : b ≤ B*s*ℓ^7 := hb.trans (by
    calc
      B*ℓ^7 ≤ (B*ℓ^7)*s := Nat.le_mul_of_pos_right _ hs
      _ = _ := by ring)
  have h8 : 8 ≤ 8*s*ℓ^7 := by nlinarith only [hl7, hs]
  nlinarith only [hmain', hL', hb', h8]

theorem sourceBox_side_bound (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0 < S.nnz)
    (hm2 : 2 ≤ S.nnz) (hunit : IsUnit (Source.realMatrix S)) (j : Fin 3) :
    sourceBox p S hm (sourceStage p S hm) j ≤ sourceSideCoefficient p*
      SourceRouting.side S (SelectedInput.input p S hm).precision*(inputLog S.nnz)^7 := by
  have h := source_scales p S hm hm2 hunit
  have hside := SourceRouting.side_pos S (SelectedInput.input p S hm).precision
  have hh := padded_side_bound (inputLog_pos S.nnz) hside h.1 h.2.1 h.2.2.2
  apply le_trans (b := 2*stageLength (sourceStage p S hm)*
    stageSpacing (sourceInput p S hm) exponent (sourceStage p S hm)*
      (2^54*129*SourceRouting.side S (SelectedInput.input p S hm).precision)+
    stageLength (sourceStage p S hm)+stageLength (sourceStage p S hm)*
      stageBuffer (sourceInput p S hm) exponent (sourceStage p S hm)+8) _ hh
  simp only [sourceBox, stageSpan, scaledSpan, sourceInput, PhysicalParameters.routingSide_eq]
  omega

theorem logFactor_le_inputLog (m : ℕ) (hm : 0 < m) :
    SelectedVolumeBounds.logFactor m ≤ 2*(inputLog m : ℝ) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hpow : (m : ℝ) ≤ (2 : ℝ)^inputLog m := by exact_mod_cast input_le_binary m
  have hlog := Real.log_le_log hm0 hpow
  rw [Real.log_pow] at hlog
  have h2 : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh
    exact hh
  have hℓ : (1 : ℝ) ≤ inputLog m := by exact_mod_cast inputLog_pos m
  have hp := mul_le_mul_of_nonneg_left h2 (show (0 : ℝ) ≤ inputLog m by positivity)
  unfold SelectedVolumeBounds.logFactor
  linarith

def routingVolumeCoefficient (p : Source.Parameters) : ℝ :=
  256*(30*SelectedVolumeBounds.precisionCoefficient p)^(3/2 : ℝ)

theorem routingVolumeCoefficient_nonneg (p : Source.Parameters) :
    0 ≤ routingVolumeCoefficient p := by
  have := SelectedVolumeBounds.precisionCoefficient_pos p
  unfold routingVolumeCoefficient
  positivity

theorem source_routing_cube_bound (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0 < S.nnz)
    (hm2 : 2 ≤ S.nnz) (hunit : IsUnit (Source.realMatrix S)) :
    (SourceRouting.side S (SelectedInput.input p S hm).precision : ℝ)^3 ≤
      routingVolumeCoefficient p*(S.nnz : ℝ)^(3/2 : ℝ)*(inputLog S.nnz : ℝ)^2 := by
  have h := SelectedVolumeBounds.side_cube_bound p S hm hm2 hunit
  have hprec := SelectedVolumeBounds.precisionCoefficient_pos p
  have hl := logFactor_le_inputLog S.nnz hm
  have hl0 := (SelectedVolumeBounds.logFactor_ge_one S.nnz hm).trans' (by norm_num : (0 : ℝ) ≤ 1)
  have hp := pow_le_pow_left₀ hl0 hl 2
  calc
    _ ≤ (64*(30*SelectedVolumeBounds.precisionCoefficient p)^(3/2 : ℝ))*
      (S.nnz : ℝ)^(3/2 : ℝ)*(2*(inputLog S.nnz : ℝ))^2 :=
      h.trans (mul_le_mul_of_nonneg_left hp (by positivity))
    _ = _ := by unfold routingVolumeCoefficient; ring

def sourceVolumeCoefficient (p : Source.Parameters) : ℝ :=
  8*(sourceSideCoefficient p : ℝ)^3*routingVolumeCoefficient p

theorem source_box_cells_bound (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0 < S.nnz)
    (hm2 : 2 ≤ S.nnz) (hunit : IsUnit (Source.realMatrix S)) :
    ((∏ j : Fin 3, sourceBox p S hm (sourceStage p S hm) j : ℕ) : ℝ) ≤
      (sourceSideCoefficient p : ℝ)^3*routingVolumeCoefficient p*
        (S.nnz : ℝ)^(3/2 : ℝ)*(inputLog S.nnz : ℝ)^23 := by
  have hprod := Finset.prod_le_prod (s := Finset.univ)
    (fun j (_ : j ∈ Finset.univ) => sourceBox_side_bound p S hm hm2 hunit j)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hprod
  have hprodR : ((∏ j : Fin 3, sourceBox p S hm (sourceStage p S hm) j : ℕ) : ℝ) ≤
      ((sourceSideCoefficient p : ℝ)*SourceRouting.side S (SelectedInput.input p S hm).precision*
        (inputLog S.nnz : ℝ)^7)^3 := by exact_mod_cast hprod
  have hc := source_routing_cube_bound p S hm hm2 hunit
  calc
    _ ≤ (sourceSideCoefficient p : ℝ)^3*
        (SourceRouting.side S (SelectedInput.input p S hm).precision : ℝ)^3*
        (inputLog S.nnz : ℝ)^21 := by convert hprodR using 1; ring
    _ ≤ (sourceSideCoefficient p : ℝ)^3*(routingVolumeCoefficient p*
        (S.nnz : ℝ)^(3/2 : ℝ)*(inputLog S.nnz : ℝ)^2)*(inputLog S.nnz : ℝ)^21 := by
      gcongr
    _ = _ := by ring

/-- Actual Euclidean Lebesgue volume, with all buffer and empty cells included. -/
theorem source_physical_volume_bound (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0 < S.nnz)
    (hm2 : 2 ≤ S.nnz) (hunit : IsUnit (Source.realMatrix S)) :
    (MeasureTheory.volume (BoxModes.openBox
      (BoxCutoff.side (sourceBox p S hm (sourceStage p S hm))))).toReal ≤
      sourceVolumeCoefficient p*(S.nnz : ℝ)^(3/2 : ℝ)*(inputLog S.nnz : ℝ)^24 := by
  rw [BoxModes.openBox_volume_toReal _ (fun j => by unfold BoxCutoff.side; positivity)]
  have hc := source_box_cells_bound p S hm hm2 hunit
  have hℓ : (1 : ℝ) ≤ inputLog S.nnz := by exact_mod_cast inputLog_pos S.nnz
  have hp : (inputLog S.nnz : ℝ)^23 ≤ (inputLog S.nnz : ℝ)^24 :=
    pow_le_pow_right₀ hℓ (by omega)
  calc
    _ = 8*((∏ j : Fin 3, sourceBox p S hm (sourceStage p S hm) j : ℕ) : ℝ) := by
      simp only [BoxCutoff.side, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin, Nat.cast_prod]
      norm_num
    _ ≤ 8*((sourceSideCoefficient p : ℝ)^3*routingVolumeCoefficient p*
        (S.nnz : ℝ)^(3/2 : ℝ)*(inputLog S.nnz : ℝ)^23) :=
      mul_le_mul_of_nonneg_left hc (by norm_num)
    _ ≤ _ := by
      unfold sourceVolumeCoefficient
      convert mul_le_mul_of_nonneg_left hp
        (show 0 ≤ 8*(sourceSideCoefficient p : ℝ)^3*routingVolumeCoefficient p*
          (S.nnz : ℝ)^(3/2 : ℝ) by have := routingVolumeCoefficient_nonneg p; positivity) using 1
      ring

#print axioms sourceBox_side_bound
#print axioms source_box_cells_bound
#print axioms source_physical_volume_bound

end Maxwell.Continuum.Parameters
