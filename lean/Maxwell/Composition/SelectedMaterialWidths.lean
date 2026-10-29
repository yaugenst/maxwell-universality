import Maxwell.Composition.SelectedGridWidths

/-! Each actual cell has at most one defect owner. Consequently scalar
coefficient widths do not grow with the number of routed sites. -/
noncomputable section
namespace Maxwell.Composition.SelectedMaterialWidths
open Maxwell.Realization Maxwell.Composition.SelectedCoefficientWidths
open Maxwell.Composition.SelectedGridWidths
open Maxwell.Spectral Maxwell.Spectral.Lattice
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 1200000

def backgroundCoefficient (R : SelectedPlatform) : ℕ :=
  Finset.univ.sup (fun c : Cell20 => rationalBitLength (R.physical.background.material c))
def baseCoefficient (p : Source.Parameters) (R : SelectedPlatform) : ℕ :=
  backgroundCoefficient R+midpointCoefficient p R+9
def materialCoefficient (p : Source.Parameters) (R : SelectedPlatform) : ℕ :=
  baseCoefficient p R+incrementCoefficient p R+9

theorem background_short (R : SelectedPlatform) (m : ℕ) (c : Cell20) :
    Source.ShortRational ((backgroundCoefficient R*unsignedBitLength (2+m):ℕ):ℝ)
      (R.physical.background.material c) := by
  have h : rationalBitLength (R.physical.background.material c) ≤ backgroundCoefficient R :=
    Finset.le_sup (f:=fun c : Cell20 => rationalBitLength (R.physical.background.material c))
      (Finset.mem_univ c)
  apply (short_of_bits h).mono
  exact_mod_cast (show backgroundCoefficient R≤backgroundCoefficient R*unsignedBitLength (2+m) by
    nlinarith [inputBitLength_pos m])

theorem sixtyFour_short : Source.ShortRational (8:ℝ) (64:ℚ) := by
  norm_num [Source.ShortRational,signedBitLength,unsignedBitLength]

variable (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0 < S.nnz) (R : SelectedPlatform)
local notation "I" => SelectedInput.input p S hm
local notation "B" => unsignedBitLength (2+S.nnz)

abbrev blocks := DecoratedDefectLayout.cellBlocks S (I).precision R.physical.basis R.physical.defect
  ((I).distance R) (R.physical.chosenBuffer S (I).precision ((I).distance R)
    ((I).zeta R) ((I).zeta_pos R) ((I).zeta_one R))

theorem blocks_disjoint : Pairwise (fun i k => Disjoint (blocks p S hm R i) (blocks p S hm R k)) :=
  DecoratedDefectLayout.disjoint_cells S (I).precision R.physical.basis R.physical.basis_injective
    R.physical.defect ((I).distance R) _ (R.physical.spacing_separates _ ((I).distance_minimum R))

theorem cell_owner_unique (c : ((I).box R).Cell)
    (i k : SourceDecoration.Vertex S (I).precision)
    (hi : c∈blocks p S hm R i) (hk : c∈blocks p S hm R k) : i=k := by
  by_contra hne
  exact Finset.disjoint_left.mp (blocks_disjoint p S hm R hne) hi hk

theorem material_cases (J : ℕ) (j : Fin J) (c : ((I).box R).Cell) :
    (((I).target R J j).material.value c = PhysicalMaterial.backgroundValue R.physical S
      (I).precision ((I).distance R) ((I).zeta R) ((I).zeta_pos R) ((I).zeta_one R) J j c) ∨
    ∃ i, c∈blocks p S hm R i ∧
      ((I).target R J j).material.value c = PhysicalMaterial.backgroundValue R.physical S
        (I).precision ((I).distance R) ((I).zeta R) ((I).zeta_pos R) ((I).zeta_one R) J j c+
        64*(I).increment R i := by
  classical
  change (PhysicalMaterial.backgroundValue R.physical S (I).precision ((I).distance R)
    ((I).zeta R) ((I).zeta_pos R) ((I).zeta_one R) J j c+
    64*∑ i : SourceDecoration.Vertex S (I).precision,
      (I).increment R i*Target.defectIndicator (blocks p S hm R i) c = _) ∨ _
  by_cases h : ∃ i, c∈blocks p S hm R i
  · obtain ⟨i,hi⟩ := h
    right
    refine ⟨i,hi,?_⟩
    change PhysicalMaterial.backgroundValue R.physical S (I).precision ((I).distance R)
      ((I).zeta R) ((I).zeta_pos R) ((I).zeta_one R) J j c+
      64*∑ k : SourceDecoration.Vertex S (I).precision,
        (I).increment R k*Target.defectIndicator (blocks p S hm R k) c = _
    rw [Target.disjoint_defect_cell_sum (blocks p S hm R) ((I).increment R)
      (fun i k hne => blocks_disjoint p S hm R hne) c i hi]
  · left
    have hz : ∀ i, c∉blocks p S hm R i := by simpa using h
    have hs : (∑ i : SourceDecoration.Vertex S (I).precision,
        (I).increment R i*Target.defectIndicator (blocks p S hm R i) c) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      unfold Target.defectIndicator
      split_ifs with hi
      · exact False.elim (hz i hi)
      · exact mul_zero _
    rw [hs,mul_zero,add_zero]

theorem base_short (hm2 : 2 ≤ S.nnz) (hunit : IsUnit (Source.realMatrix S))
    (j : Fin (2^(I).randomBits R)) (c : ((I).box R).Cell) :
    Source.ShortRational ((baseCoefficient p R*B:ℕ):ℝ)
      (PhysicalMaterial.backgroundValue R.physical S (I).precision ((I).distance R)
        ((I).zeta R) ((I).zeta_pos R) ((I).zeta_one R) _ j c) := by
  have h := (background_short R S.nnz (siteMod20 (Target.latticeCell c))).add
    (sixtyFour_short.mul (midpoint_short p S hm R hm2 hunit j))
  change Source.ShortRational _ (PhysicalMaterial.backgroundValue R.physical S (I).precision
    ((I).distance R) ((I).zeta R) ((I).zeta_pos R) ((I).zeta_one R) _ j c) at h
  apply h.mono
  have hb := inputBitLength_pos S.nnz
  unfold baseCoefficient
  exact_mod_cast (show backgroundCoefficient R*B+(8+midpointCoefficient p R*B)+1≤
      (backgroundCoefficient R+midpointCoefficient p R+9)*B by nlinarith)

theorem material_short (hm2 : 2 ≤ S.nnz) (hunit : IsUnit (Source.realMatrix S))
    (j : Fin (2^(I).randomBits R)) (c : ((I).box R).Cell) :
    Source.ShortRational ((materialCoefficient p R*B:ℕ):ℝ)
      (((I).target R _ j).material.value c) := by
  have hb := base_short p S hm R hm2 hunit j c
  rcases material_cases p S hm R _ j c with h | ⟨i,_,h⟩
  · rw [h]
    apply hb.mono
    exact_mod_cast Nat.mul_le_mul_right B
      (show baseCoefficient p R≤materialCoefficient p R by unfold materialCoefficient; omega)
  · rw [h]
    have hv := sixtyFour_short.mul (increments_short p S hm R hm2 hunit i)
    apply (hb.add hv).mono
    have hB := inputBitLength_pos S.nnz
    unfold materialCoefficient
    exact_mod_cast (show baseCoefficient p R*B+(8+incrementCoefficient p R*B)+1≤
      (baseCoefficient p R+incrementCoefficient p R+9)*B by nlinarith)

end Maxwell.Composition.SelectedMaterialWidths
