import Maxwell.Continuum.ChebyshevWaveCacheFrame

/-! Charged preparation of one wave-cache entry from the actual outer
countdown. The code contains no precision- or index-dependent literal. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalDataflow RationalTaylor
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

def cacheLoadCode : Code := .seq (program cacheResetInstructions)
  (.seq (NaturalChannel.code .positive 201 12) (WordReplace.code 681 680))
def cacheLoadCost (B indexLength grid : ℕ) : ℕ :=
  12*operationCost (B+1)+31*indexLength+15*grid.bits.length+61
def cacheLoadWorkspace : Finset ℕ := insert 680 (RationalDataflow.workspace ids)

theorem cacheLoad_subset_encoded : cacheLoadWorkspace⊆encodedWorkspace := by
  apply Finset.insert_subset
  · simp [encodedWorkspace,cosineWorkspace,sumWorkspace]
  · exact arithmetic_subset_cosine.trans (Finset.subset_insert _ _)

theorem cacheReset_program_width (B : ℕ) : programWidth cacheResetInstructions (fun _ => B) ≤ B+1 := by
  simp [cacheResetInstructions,programWidth,RationalDataflow.Instruction.resultWidth,Parts.literal]

theorem cacheLoad_executes (Q P grid B : ℕ) (v : ℕ→Parts) (hw : WidthBank ids B v)
    (input : List Bool) (tape : ℕ→Bool) (xs : List Bool) (s : Store) (hs : LoopReady Q P v s)
    (hindex : BankArray.Word s.val 201 xs) (hz : Blank s.val 680) (hgrid : Word s.val 681 grid) :
    ∃cost t,Executes input tape cacheLoadCode cost s t ∧ cost ≤ cacheLoadCost B xs.length grid ∧
      LoopReady Q P (cacheLoaded (addressValue xs) v) t ∧ Word t.val 680 grid ∧
      BinaryPrecision.Frame cacheLoadWorkspace s.val t.val := by
  have htrace := inferred_widthTrace ids cacheResetInstructions cacheResetInstructions_valid
    (fun _ => B) v hw _ (hw.mono (by omega)) (cacheReset_program_width B)
  obtain ⟨c0,s0,e0,hc0,r0,f0⟩ := program_executes ids cacheResetInstructions cacheResetInstructions_valid
    v (B+1) htrace input tape s hs.ready
  have lr0 : LoopReady Q P (cacheResetValues v) s0 := hs.arithmetic_frame f0 r0
  have index0 := BankArray.word_of_eq
    (f0.tapes 201 (RationalDataflow.outside_workspace ids 201 (by decide))) hindex
  obtain ⟨c1,s1,e1,hc1,r1,f1⟩ := NaturalChannel.executes ids .positive 201 12 (by decide) (by decide)
    (cacheResetValues v) xs input tape s0 lr0.ready index0
  have veq : Function.update (cacheResetValues v) 12
      (NaturalChannel.replace .positive (cacheResetValues v 12) (addressValue xs))=
        cacheLoaded (addressValue xs) v := by
    simp [cacheLoaded,NaturalChannel.replace,cacheResetValues_eq,Parts.literal]
  rw [veq] at r1
  have fa1 : BinaryPrecision.Frame (RationalDataflow.workspace ids) s0.val s1.val :=
    f1.mono (by
      intro i hi
      have he : i=positivePort 12 := by simpa only [NaturalChannel.port,Finset.mem_singleton] using hi
      subst i
      exact Finset.mem_union_right _ (NaturalChannel.port_mem .positive ids 12 (by decide)))
  have lr1 := lr0.arithmetic_frame fa1 r1
  have f01 := f0.trans fa1
  have grid1 := word_of_eq (f01.tapes 681 (RationalDataflow.outside_workspace ids 681 (by decide))) hgrid
  have z1 := blank_of_eq (f01.tapes 680 (RationalDataflow.outside_workspace ids 680 (by decide))) hz
  obtain ⟨t,e2,n2,f2⟩ := WordReplace.executes 681 680 (by decide) input tape grid.bits [] s1 grid1
    ((zero_word_iff_blank _ _).mpr z1)
  have e2' : Executes input tape (WordReplace.code 681 680) (15*grid.bits.length+21) s1 t := by
    simpa only [List.length_nil,Nat.mul_zero,Nat.zero_add] using e2
  have cf2 := StoredParts.copy_frame f2
  refine ⟨c0+(c1+(15*grid.bits.length+21)),t,e0.seq (e1.seq e2'),?_,lr1.counter_frame cf2,n2,
    (f01.mono (Finset.subset_insert _ _)).trans (cf2.mono (by simp))⟩
  have hc0' : c0 ≤ 12*operationCost (B+1)+1 := by
    simpa only [show cacheResetInstructions.length=12 by rfl] using hc0
  have hz' : dataValues (cacheResetValues v) (NaturalChannel.port .positive 12)=0 := by
    simp [NaturalChannel.port,dataValues_positive,cacheResetValues_eq,Parts.literal]
  rw [hz'] at hc1
  simp only [Nat.zero_bits,List.length_nil] at hc1
  unfold cacheLoadCost
  omega

#print axioms cacheLoad_executes
end Maxwell.Continuum.Profile.WaveMachine.Runtime
