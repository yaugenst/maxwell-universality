import Maxwell.Continuum.FourierTensorModePrepare
import Maxwell.Continuum.RationalDataflowResetList
import Maxwell.Continuum.NatAssignCleanup

/-! The row loop retains only the physical scale, frequency scale, radius,
and array length. Every other computed work word is explicitly reset. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime.ModePrepare
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow PartArray Calibration
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

def rationalTargets : List ℕ := List.range' 2 26
def naturalTargets : List ℕ := [310,312,313,314,315,316,317,318,319,320,321]
def resetCode : Code := .seq (resetList rationalTargets).code
  (NatAssign.code (NatAssign.clearList naturalTargets))
def canonical (v : ℕ→Parts) (i : ℕ) : Parts :=
  if 2 ≤ i ∧ i<28 then Parts.literal 0 else v i

theorem rationalTargets_mem (i : ℕ) : i∈rationalTargets ↔ 2 ≤ i ∧ i<28 := by
  simp only [rationalTargets,List.mem_range',Nat.one_mul]
  constructor
  · rintro ⟨k,hk,rfl⟩
    omega
  · intro hi
    exact ⟨i-2,by omega,by omega⟩

theorem canonical_width (v : ℕ→Parts) (W : ℕ) (hW : 1≤W) (hv : WidthBank RowArithmetic.bank W v) :
    WidthBank RowArithmetic.bank W (canonical v) := by
  intro i hi
  unfold canonical
  split_ifs
  · exact (show (Parts.literal 0).Width 1 by norm_num [Parts.Width,Parts.literal]).mono hW
  · exact hv i hi

theorem canonical_good (v : ℕ→Parts) (hv : Good RowArithmetic.bank v) :
    Good RowArithmetic.bank (canonical v) := by
  intro i hi
  unfold canonical
  split_ifs
  · exact Parts.literal_valid 0
  · exact hv i hi

theorem canonical_idempotent (v : ℕ→Parts) : canonical (canonical v)=canonical v := by
  funext i
  by_cases hi : 2 ≤ i ∧ i<28 <;> simp [canonical,hi]

theorem reset_prepared (P R : ℕ) (a : Table (2*aliasArraySize R)) (j : Fin 3)
    (r : Fin (RowArithmetic.rowCount R)) (v : ℕ→Parts) :
    (resetList rationalTargets).evaluate (values P R a j r v)=canonical v := by
  funext i
  simp only [resetList_values,rationalTargets_mem]
  unfold canonical
  by_cases hi : 2 ≤ i ∧ i<28
  · simp [hi]
  · simp only [hi,ite_false,values,ModeDecode.rowValues_eq]
    rw [RowArithmetic.output_other _ _ i (by
      simp only [Finset.mem_insert,Finset.mem_singleton];omega)]
    simp (disch := omega) only [RowArithmetic.loaded,Function.update_of_ne]

theorem index_size (j : Fin 3) (R size row : ℕ) : ModeIndex.values j R size row 322=size := by
  simp [ModeIndex.values,ModeIndex.instructions,ModeIndex.initial,NatAssign.values,
    NatAssign.Instruction.update,NatAssign.Instruction.target,NatAssign.Instruction.value]

theorem after_radius (R size row : ℕ) (j : Fin 3) (v : ℕ→Parts) :
    ModeDecode.after v (ModeIndex.values j R size row) 311=R := by
  rw [ModeDecode.after,ModeDecode.coordinateLoad_low _ _ (by decide),
    ArrayDecodeMachine.output_radius,ModeDecode.combined_at _ _ _ (by decide),ModeIndex.values_radius]

theorem after_size (R size row : ℕ) (j : Fin 3) (v : ℕ→Parts) :
    ModeDecode.after v (ModeIndex.values j R size row) 322=size := by
  rw [ModeDecode.after,ModeDecode.coordinateLoad_low _ _ (by decide),
    ArrayDecodeMachine.output_outside _ _ (by decide),
    ModeDecode.combined_at _ _ _ (by decide),index_size]

theorem reset_naturals (R size row : ℕ) (j : Fin 3) (v : ℕ→Parts) (i : ℕ)
    (hi : i∈ModeIndex.ports) :
    NatAssign.values (NatAssign.clearList naturalTargets)
      (ModeDecode.after v (ModeIndex.values j R size row)) i=ModeIndex.initial R size 0 i := by
  rw [NatAssign.clearList_values]
  by_cases h311 : i=311
  · subst i
    simp only [naturalTargets,List.mem_cons,List.not_mem_nil,or_false,
      after_radius,ModeIndex.initial]
    rfl
  · by_cases h322 : i=322
    · subst i
      simp only [naturalTargets,List.mem_cons,List.not_mem_nil,or_false,
        after_size,ModeIndex.initial]
      rfl
    · have hmem : i∈naturalTargets := by
        simp only [ModeIndex.ports,Finset.mem_Icc] at hi
        simp only [naturalTargets,List.mem_cons,List.not_mem_nil,or_false]
        omega
      simp only [hmem,ite_true,ModeIndex.initial,h311,h322,ite_false]
      split_ifs <;> rfl

#print axioms reset_prepared
#print axioms reset_naturals
end Maxwell.Continuum.Profile.WaveMachine.Runtime.ModePrepare
