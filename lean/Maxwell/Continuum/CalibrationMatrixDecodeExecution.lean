import Maxwell.Continuum.CalibrationMatrixDecodeValues
import Maxwell.Continuum.CalibrationMatrixEntryExecution

/-! Both row and column coordinates of a literal cached matrix entry are
obtained by fixed runtime quotient/remainder code and charged register copies. -/

namespace Maxwell.Continuum.Calibration.ArrayDecodeMachine

open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
set_option maxHeartbeats 4500000
set_option maxRecDepth 16384

theorem ids_subset {S T : Finset ℕ} (hST : S ⊆ T) : ids S ⊆ ids T := by
  intro k hk
  rcases Finset.mem_union.mp hk with hp | hw
  · obtain ⟨i,hi,hk⟩ := Finset.mem_biUnion.mp hp
    exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨i,hST hi,hk⟩)
  · exact Finset.mem_union_right _ hw

theorem output_work_zero (n : ℕ → ℕ) (hn : ∀ k ∈ NaturalQuotient.workPorts, n k=0) :
    ∀ k ∈ NaturalQuotient.workPorts, output n k=0 := by
  intro k hk
  rw [output_outside n k ?_,hn k hk]
  simp only [NaturalQuotient.workPorts,Finset.mem_insert,Finset.mem_singleton] at hk
  simp only [ports,Finset.mem_Icc]
  omega

theorem rowStart_work_zero (n : ℕ → ℕ) (hn : ∀ k ∈ NaturalQuotient.workPorts, n k=0) :
    ∀ k ∈ NaturalQuotient.workPorts, rowStart n k=0 := by
  intro k hk
  have hh := hk
  simp only [NaturalQuotient.workPorts,Finset.mem_insert,Finset.mem_singleton] at hh
  rw [rowStart,Function.update_of_ne (show k≠310 by omega),columnNaturals_small n k (by omega)]
  exact output_work_zero n hn k hk

theorem rowCopy_values (n : ℕ → ℕ) :
    NatAssign.values [.copy 321 310] (columnNaturals n)=rowStart n := by
  simp only [NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,
    NatAssign.Instruction.value]
  rw [columnNaturals_small n 321 (by decide),output_outside n 321 (by decide)]
  rfl

theorem rowStart_width (allIds : Finset ℕ) (hdecode : ports ⊆ allIds) (hrow : 321 ∈ allIds)
    (n : ℕ → ℕ) (B : ℕ) (hw : ∀ k ∈ allIds, (n k).bits.length≤B) :
    ∀ k ∈ allIds, (rowStart n k).bits.length≤2*B+8 := by
  have h0 := output_width n allIds hdecode B hw
  have h1 := columnLoad_width (output n) allIds hdecode (2*B+8) (by omega) h0
  exact nat_update_width _ allIds _ _ _ h1 ((hw 321 hrow).trans (by omega))

theorem matrixNaturals_width (allIds : Finset ℕ) (hdecode : ports ⊆ allIds) (hrow : 321 ∈ allIds)
    (n : ℕ → ℕ) (B : ℕ) (hw : ∀ k ∈ allIds, (n k).bits.length≤B) :
    ∀ k ∈ allIds, (matrixNaturals n k).bits.length≤4*B+24 := by
  have h1 := rowStart_width allIds hdecode hrow n B hw
  have h2 := output_width (rowStart n) allIds hdecode (2*B+8) h1
  have h3 := coordinateLoad_width (output (rowStart n)) allIds hdecode (2*(2*B+8)+8) (by omega) h2
  simpa only [matrixNaturals,show 2*(2*B+8)+8=4*B+24 by omega] using h3

theorem frame_blank_four (allIds : Finset ℕ) (hIds : ∀ k ∈ allIds, 10≤k)
    (s t : Store) (hframe : BinaryPrecision.Frame ({0,1,2,3} ∪ allIds) s.val t.val)
    (hblank : RationalAccumulator.Blank s.val 4) : RationalAccumulator.Blank t.val 4 := by
  apply RationalAccumulator.blank_of_eq (hframe.tapes 4 ?_) hblank
  have hn : 4∉allIds := fun h => by have := hIds 4 h; omega
  simp [hn]

theorem extendFrame (allIds : Finset ℕ) (s t : Store)
    (hframe : BinaryPrecision.Frame ({0,1,2,3} ∪ allIds) s.val t.val) :
    BinaryPrecision.Frame ({0,1,2,3,4} ∪ allIds) s.val t.val :=
  hframe.mono (by intro k hk; simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hk ⊢; tauto)

theorem matrixDecode_executes (allIds : Finset ℕ) (hIds : ∀ k ∈ allIds, 10≤k)
    (hdecode : ports ⊆ allIds) (hwork : NaturalQuotient.workPorts ⊆ allIds)
    (hparts : ids RawFree.neighborRegisters ⊆ allIds) (hrow : 321∈allIds)
    (n : ℕ → ℕ) (v : ℕ → Parts)
    (hn : ∀ k ∈ ids RawFree.neighborRegisters, n k=dataValues v k)
    (hzwork : ∀ k ∈ NaturalQuotient.workPorts, n k=0)
    (hg : Good RawFree.neighborRegisters v) (B : ℕ) (hB : 2≤B)
    (hw : ∀ k ∈ allIds, (n k).bits.length≤B)
    (R : ℕ) (i j : Fin (aliasArraySize R)) (hR : n 311=R) (hi : n 321=i.val) (hj : n 310=j.val)
    (input : List Bool) (tape : ℕ → Bool) (s : Store) (hs : NatAssign.Bank allIds n s.val)
    (hz : ∀ k, k<5 → RationalAccumulator.Blank s.val k) :
    ∃ cost t, Executes input tape matrixDecodeCode cost s t ∧ cost≤2^116*(B+10)^2 ∧
      NatAssign.Bank allIds (matrixNaturals n) t.val ∧
      RationalDataflow.Ready RawFree.neighborRegisters (matrixParts v n) t ∧
      Good RawFree.neighborRegisters (matrixParts v n) ∧
      WidthBank RawFree.neighborRegisters (4*B+24) (matrixParts v n) ∧
      (∀ k, RawFree.coordinates (matrixParts v n) k=RawFree.coordinatePart R i k) ∧
      (matrixParts v n 23).value=((arrayPolarizationAt R i).val : ℚ) ∧
      (∀ k, RawFree.columnCoordinates (matrixParts v n) k=RawFree.coordinatePart R j k) ∧
      (matrixParts v n 24).value=((arrayPolarizationAt R j).val : ℚ) ∧
      BinaryPrecision.Frame ({0,1,2,3,4} ∪ allIds) s.val t.val ∧
      RationalAccumulator.Blank t.val 4 := by
  have ge4 (k : ℕ) (hk : k ∈ allIds) : 4≤k := by have := hIds k hk; omega
  obtain ⟨c0,u0,e0,hc0,b0,z0,f0⟩ := executes allIds hIds hdecode hwork n hzwork B hB hw input tape s hs hz
  have w0 := output_width n allIds hdecode B hw
  obtain ⟨c1,u1,e1,hc1,b1,ready1,f1⟩ := columnLoad_executes allIds ge4 hdecode hparts
    (output n) v (output_agrees_all _ n v hn) (2*B+8) (by omega) w0 input tape u0 b0
    (fun k hk => z0 k (by omega))
  have z14 := frame_blank_four allIds hIds u0 u1 f1 (z0 4 (by decide))
  have w1 := columnLoad_width (output n) allIds hdecode (2*B+8) (by omega) w0
  have rowValid : ∀ (a : NatAssign.Instruction), a ∈ [.copy 321 310] → a.Valid allIds := by
    simp [NatAssign.Instruction.Valid,hrow,hdecode (by decide : 310∈ports)]
  obtain ⟨c2,u2,e2,hc2,b2,z2,f2⟩ := fixedBankStage_executes allIds ge4 [.copy 321 310]
    rowValid (by decide) (columnNaturals n) (2*B+8) w1
    (by simp [NatAssign.Instruction.literalWidth]) input tape u1 b1 ready1.2
  rw [rowCopy_values] at b2
  have z24 := frame_blank_four allIds hIds u1 u2 f2 z14
  have blank2 (k : ℕ) (hk : k<5) : RationalAccumulator.Blank u2.val k := by
    by_cases hlt : k<4
    · exact z2 k hlt
    · have he : k=4 := by omega
      exact he ▸ z24
  have w2 := rowStart_width allIds hdecode hrow n B hw
  obtain ⟨c3,u3,e3,hc3,b3,z3,f3⟩ := executes allIds hIds hdecode hwork (rowStart n)
    (rowStart_work_zero n hzwork) (2*B+8) (by omega) w2 input tape u2 b2 blank2
  have w3 := output_width (rowStart n) allIds hdecode (2*B+8) w2
  rw [show 2*(2*B+8)+8=4*B+24 by omega] at w3
  have agree3 := output_agrees_all RawFree.neighborRegisters (rowStart n)
    (columnParts v (output n)) (rowStart_agrees _ n v hn)
  have small := ids_subset RawFree.stage_subset_neighbors
  obtain ⟨c4,t,e4,hc4,b4,ready4,f4⟩ := coordinateLoad_executes allIds ge4 hdecode
    (small.trans hparts) (output (rowStart n)) (columnParts v (output n))
    (fun k hk => agree3 k (small hk)) (4*B+24) (by omega) w3 input tape u3 b3
    (fun k hk => z3 k (by omega))
  have agree4 := matrixNaturals_agrees RawFree.neighborRegisters n v hn
  have ready : RationalDataflow.Ready RawFree.neighborRegisters (matrixParts v n) t := by
    refine ⟨?_,ready4.2⟩
    intro k hk
    have hb := b4 k (hparts hk)
    change RationalAccumulator.Word t.val k (matrixNaturals n k) at hb
    simpa only [agree4 k hk] using hb
  have w4 := matrixNaturals_width allIds hdecode hrow n B hw
  obtain ⟨rowc,rowp⟩ := matrixParts_row n v R i j hR hi hj
  obtain ⟨colc,colp⟩ := matrixParts_column n v R i j hR hi hj
  refine ⟨c0+(c1+(c2+(c3+c4))),t,e0.seq (e1.seq (e2.seq (e3.seq e4))),?_,b4,ready,
    matrixParts_good _ n v hg,data_width_all _ _ _ _ agree4 (fun k hk => w4 k (hparts hk)),
    rowc,rowp,colc,colp,f0.trans ((extendFrame allIds u0 u1 f1).trans
      ((extendFrame allIds u1 u2 f2).trans (f3.trans (extendFrame allIds u3 t f4)))),
    frame_blank_four allIds hIds u3 t f4 (z3 4 (by decide))⟩
  change c2≤2^96*(2*B+8+2)^2 at hc2
  have hs0 : (B+5)^2≤(B+10)^2 := Nat.pow_le_pow_left (by omega) 2
  have hs1 : (2*B+8+2)^2≤4*(B+10)^2 := by nlinarith [Nat.zero_le B]
  have hs3 : (2*B+8+5)^2≤4*(B+10)^2 := by nlinarith [Nat.zero_le B]
  have hs4 : (4*B+24+2)^2≤16*(B+10)^2 := by nlinarith [Nat.zero_le B]
  nlinarith only [hc0,hc1,hc2,hc3,hc4,hs0,hs1,hs3,hs4,Nat.zero_le ((B+10)^2)]

#print axioms matrixDecode_executes

end Maxwell.Continuum.Calibration.ArrayDecodeMachine
