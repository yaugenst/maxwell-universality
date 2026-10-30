import Maxwell.Continuum.ParameterVolume
import Maxwell.Composition.SourceSeedSupport

/-! Counts for the actual decorated well records and nonzero source entries. -/

noncomputable section
namespace Maxwell.Continuum.Parameters
open Maxwell.Composition
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1000000

def sharpRoutingCoefficient (p : Source.Parameters) : ℝ :=
  64*(60*SelectedVolumeBounds.precisionCoefficient p)^(3/2 : ℝ)

theorem sharpRoutingCoefficient_nonneg (p : Source.Parameters) : 0 ≤ sharpRoutingCoefficient p := by
  have := SelectedVolumeBounds.precisionCoefficient_pos p
  unfold sharpRoutingCoefficient
  positivity

theorem source_routing_cube_sharp (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0 < S.nnz)
    (hm2 : 2 ≤ S.nnz) (hunit : IsUnit (Source.realMatrix S)) :
    (SourceRouting.side S (SelectedInput.input p S hm).precision : ℝ)^3 ≤
      sharpRoutingCoefficient p*(S.nnz : ℝ)^(3/2 : ℝ)*(inputLog S.nnz : ℝ)^(3/2 : ℝ) := by
  let I := SelectedInput.input p S hm
  have hc := Maxwell.Logical.sourceCircuit_size_two_le S hm2 I.precision
  have hv : 0 < Fintype.card (SourcePositive.Vertex S I.precision) := by
    change 0 < Fintype.card ((Fin _ ⊕ Fin _) ⊕ _)
    simp only [Fintype.card_sum,Fintype.card_fin]
    omega
  have hq := Maxwell.Cost.portSide_cube_bound _ hv
  change (SourceRouting.side S I.precision : ℝ)^3 ≤ _ at hq
  have hu : (Fintype.card (SourcePositive.Vertex S I.precision) : ℝ) ≤
      30*(S.nnz : ℝ)*(I.precision+1) := by
    exact_mod_cast SourceRouting.original_vertices_le S I.precision (Source.dimension_le_nnz S hunit)
  have hp := SelectedVolumeBounds.precision_log_bound p S hm
  have hprec := SelectedVolumeBounds.precisionCoefficient_pos p
  have hp' := hp.trans (mul_le_mul_of_nonneg_left (logFactor_le_inputLog S.nnz hm) hprec.le)
  have hU := hu.trans (mul_le_mul_of_nonneg_left hp' (by positivity))
  have hpow := Real.rpow_le_rpow (by positivity) hU (by norm_num : (0 : ℝ) ≤ 3/2)
  have hid : (30*(S.nnz : ℝ)*(SelectedVolumeBounds.precisionCoefficient p*
      (2*(inputLog S.nnz : ℝ))))^(3/2 : ℝ) =
      (60*SelectedVolumeBounds.precisionCoefficient p)^(3/2 : ℝ)*
      (S.nnz : ℝ)^(3/2 : ℝ)*(inputLog S.nnz : ℝ)^(3/2 : ℝ) := by
    rw [show 30*(S.nnz : ℝ)*(SelectedVolumeBounds.precisionCoefficient p*
      (2*(inputLog S.nnz : ℝ))) =
      (60*SelectedVolumeBounds.precisionCoefficient p)*(S.nnz : ℝ)*(inputLog S.nnz : ℝ) by ring,
      Real.mul_rpow (by positivity) (by positivity),Real.mul_rpow (by positivity) (by positivity)]
  rw [hid] at hpow
  apply hq.trans
  convert mul_le_mul_of_nonneg_left hpow (by norm_num : (0 : ℝ) ≤ 64) using 1
  unfold sharpRoutingCoefficient
  ring

def sourceRecordCoefficient (p : Source.Parameters) : ℝ := 4*80625*sharpRoutingCoefficient p

theorem sourceRecordCoefficient_nonneg (p : Source.Parameters) : 0 ≤ sourceRecordCoefficient p := by
  have := sharpRoutingCoefficient_nonneg p
  unfold sourceRecordCoefficient
  positivity

/-- The sharp count includes every physical midpoint mediator. -/
theorem source_well_record_count (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0 < S.nnz)
    (hm2 : 2 ≤ S.nnz) (hunit : IsUnit (Source.realMatrix S)) :
    ((sourceInput p S hm).J : ℝ) ≤ sourceRecordCoefficient p*
      (S.nnz : ℝ)^(3/2 : ℝ)*(inputLog S.nnz : ℝ)^(3/2 : ℝ) := by
  let n := (SelectedInput.input p S hm).precision
  have hV := (SourceRouting.vertex_card_le_box S n).trans (SourceRouting.box_volume_le_cube S n)
  have hW := (sourceWell_card S n).trans (Nat.mul_le_mul_left 4 hV)
  have hh : ((sourceInput p S hm).J : ℝ) ≤ 4*80625*(SourceRouting.side S n : ℝ)^3 := by
    change (Fintype.card (SourceDecoration.Vertex S n) : ℝ) ≤ _
    have hh : (Fintype.card (SourceDecoration.Vertex S n) : ℝ) ≤ 4*(80625*(SourceRouting.side S n : ℝ)^3) := by exact_mod_cast hW
    convert hh using 1
    ring
  apply hh.trans
  convert mul_le_mul_of_nonneg_left (source_routing_cube_sharp p S hm hm2 hunit)
    (by norm_num : (0 : ℝ) ≤ 4*80625) using 1
  unfold sourceRecordCoefficient
  ring

/-- The exact nonzero support of the source emitted on the decorated graph. -/
def sourceNonzeroEntries (S : Source.SparseSystem) (n : ℕ) : Finset (SourceDecoration.Vertex S n) :=
  Finset.univ.filter fun v => SourceRational.decorated S n v ≠ 0

theorem source_nonzero_count (S : Source.SparseSystem) (n : ℕ)
    (hunit : IsUnit (Source.realMatrix S)) : (sourceNonzeroEntries S n).card ≤ S.nnz := by
  classical
  have hsub : sourceNonzeroEntries S n ⊆ Finset.univ.image (SourceSeedSupport.vertex S n) := by
    intro v hv
    obtain ⟨i,hi⟩ := SourceSeedSupport.source_support S n v (Finset.mem_filter.mp hv).2
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,hi⟩
  calc
    _ ≤ (Finset.univ.image (SourceSeedSupport.vertex S n)).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Fin S.n)).card := Finset.card_image_le
    _ = S.n := by simp
    _ ≤ S.nnz := Source.dimension_le_nnz S hunit

#print axioms source_routing_cube_sharp
#print axioms source_well_record_count
#print axioms source_nonzero_count

end Maxwell.Continuum.Parameters
