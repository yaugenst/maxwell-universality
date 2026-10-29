import Maxwell.Cost.CalibrationMatrix.GenerationCell
import Maxwell.Cost.CalibrationMatrix.GenerationLoopState

namespace Maxwell.Cost.CalibrationMatrix.Generation
open Structured BankArray
open RationalAccumulator (Blank)
open Maxwell.Defect.FiniteStencil Maxwell.Spectral.Lattice
open scoped BigOperators
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

def loopBody (material : Cell20 → ℚ) (z : ℚ) (D : ℕ) : Code :=
  .seq (cellCode material z D) (incrementCode 102)

def loopCode (material : Cell20 → ℚ) (z : ℚ) (D : ℕ) : Code :=
  .seq (CountedShifted.code 136 (loopBody material z D)) (.call (TapeOps.clear 136))

def iterationCost (material : Cell20 → ℚ) (z : ℚ) (D B : ℕ) : ℕ :=
  cellCost material z D B+12*B+18

def loopCost (R : ℕ) (material : Cell20 → ℚ) (z : ℚ) (D B : ℕ) : ℕ :=
  let count := (3*cubeWidth R^3)^2
  (count+1)*(13*count.bits.length+15)+count*iterationCost material z D B+6*count.bits.length+4

private theorem body_executes (input : List Bool) (tape : ℕ → Bool) (R : ℕ)
    (material : Cell20 → ℚ) (z : ℚ) (D B : ℕ) (d : Data R)
    (hfit : d.radix.length+d.dimension.length+((3*cubeWidth R^3)^2).bits.length+1 ≤ addressValue d.width)
    (htable : MaterialTable.outputBits 34 (MaterialEntry.table material z D) ≤ addressValue d.width)
    (hsize : d.Sized B) (hcountlen : ((3*cubeWidth R^3)^2).bits.length ≤ B)
    (initial : BitRAMState) (n : ℕ) (xs : List Bool) (origin : ℤ) (s : Store)
    (hinv : Invariant d material z D initial (n+1) s)
    (hcounter : s.val.tapes 136 = BitTape.shifted xs origin) :
    ∃ cost t, Executes input tape (loopBody material z D) cost s t ∧
      Invariant d material z D initial n t ∧
      t.val.tapes 136 = BitTape.shifted xs origin ∧ cost ≤ iterationCost material z D B := by
  let count := (3*cubeWidth R^3)^2
  obtain ⟨hn,index,hindex,hlen,hs,hw,hp,hm,hfr,hout⟩ := hinv
  let k : Fin count := ⟨count-(n+1),by dsimp [count] at *; omega⟩
  obtain ⟨a,m,hca,ea,hms,hmwork,hmm,hmp,hmn,hf⟩ :=
    cell_executes input tape R material z D B d (row R k) (column R k) k
      (row_column R k) index hindex (by omega) htable hsize (by omega) _ _ s hs hw hp hm
  obtain ⟨b,t,hcb,eb,hti,_,htm,_,htapes,hg⟩ := increment_bank 102 (by decide)
    input tape index m hms.index hmwork.scratch
  have hnew : addressValue (Increment.bits index) = count-n := by rw [Increment.bits_value,hindex]; dsimp [count]; omega
  have hpower : count < 2^count.bits.length := by simpa only [Nat.size_eq_bits_len] using Nat.lt_size_self count
  have hnewlen : (Increment.bits index).length ≤ count.bits.length :=
    increment_length_bound index count.bits.length hlen (by dsimp [count] at *; omega)
  have hprefix : count-n = k.val+1 := by dsimp [k]; omega
  have hpost : Workspace t.val := workspace_of_tapes hmwork (by
    intro q hq
    apply htapes q
    intro heq; subst q
    exact (show 102 ∉ work by decide) hq)
  have hincframe : LoopFrame m.val t.val :=
    ⟨hg.1,hg.2.1,hg.2.2.1,fun q _ h102 _ => htapes q h102⟩
  have houtcell : OutputOutside d.output count (addressValue d.width) s.val m.val :=
    OutputOutside.of_write k _ _ (FixedWidth.bits_length _ _) (FixedWidth.bits_length _ _) hmm
  refine ⟨a+b,t,ea.seq eb,?_,?_,by dsimp [iterationCost]; omega⟩
  · refine ⟨by omega,Increment.bits index,hnew,hnewlen,hms.increment htapes hti,hpost,?_,?_,
      hfr.trans ((LoopFrame.of_cell hf).trans hincframe),
      (hout.trans houtcell).trans (OutputOutside.of_memory htm)⟩
    · rw [htm]
      have hp' := hmp
      rw [← positiveWords_get R material z D (addressValue d.width) k,GenerationPrefix.step _ _ k] at hp'
      simpa only [show (3*cubeWidth R^3)^2-n = k.val+1 from hprefix] using hp'
    · rw [htm]
      have hn' := hmn
      rw [← negativeWords_get R material z D (addressValue d.width) k,GenerationPrefix.step _ _ k] at hn'
      simpa only [show (3*cubeWidth R^3)^2-n = k.val+1 from hprefix] using hn'
  · exact (htapes 136 (by decide)).trans ((hf.tapes 136 (by decide)).trans hcounter)

/-- Fill both dense signed matrix arrays from their actual flattened cursor.
Initial array contents are arbitrary memory, represented only by a logical
snapshot; no input matrix or entry oracle is assumed. -/
theorem loop_executes (input : List Bool) (tape : ℕ → Bool) (R : ℕ)
    (material : Cell20 → ℚ) (z : ℚ) (D B : ℕ) (d : Data R)
    (hfit : d.radix.length+d.dimension.length+((3*cubeWidth R^3)^2).bits.length+1 ≤ addressValue d.width)
    (htable : MaterialTable.outputBits 34 (MaterialEntry.table material z D) ≤ addressValue d.width)
    (hsize : d.Sized B) (hcountlen : ((3*cubeWidth R^3)^2).bits.length ≤ B)
    (index : List Bool) (hindex : addressValue index = 0)
    (hilen : index.length ≤ ((3*cubeWidth R^3)^2).bits.length)
    (origin : ℤ) (s : Store) (hs : Stored d index s.val) (hw : Workspace s.val)
    (hcounter : s.val.tapes 136 = BitTape.shifted ((3*cubeWidth R^3)^2).bits origin) :
    ∃ cost t finalIndex, cost ≤ loopCost R material z D B ∧
      Executes input tape (loopCode material z D) cost s t ∧
      addressValue finalIndex = (3*cubeWidth R^3)^2 ∧
      finalIndex.length ≤ ((3*cubeWidth R^3)^2).bits.length ∧
      Stored d finalIndex t.val ∧ Workspace t.val ∧ Blank t.val 136 ∧
      BitArray.Represents t.val.memory (addressValue d.positiveBase) (addressValue d.width)
        (positiveWords R material z D (addressValue d.width)) ∧
      BitArray.Represents t.val.memory (addressValue d.negativeBase) (addressValue d.width)
        (negativeWords R material z D (addressValue d.width)) ∧
      LoopFrame s.val t.val ∧
      OutputOutside d.output ((3*cubeWidth R^3)^2) (addressValue d.width) s.val t.val := by
  let count := (3*cubeWidth R^3)^2
  let inv := Invariant d material z D s.val
  have hinit : inv count s := by
    refine ⟨le_rfl,index,by simpa [count] using hindex,hilen,hs,hw,?_,?_,
      LoopFrame.refl _,OutputOutside.refl _ _ _ _⟩
    · simpa only [count,Nat.sub_self,GenerationPrefix.zero] using
        BitArray.snapshot_represents s.val.memory (addressValue d.positiveBase) (addressValue d.width) count
    · simpa only [count,Nat.sub_self,GenerationPrefix.zero] using
        BitArray.snapshot_represents s.val.memory (addressValue d.negativeBase) (addressValue d.width) count
  obtain ⟨a,m,finalCount,ea,hm,hmc,hmcl,_,hca⟩ := CountedShifted.executes 136 origin
    (loopBody material z D) input tape inv (fun _ => iterationCost material z D B)
    (invariant_stable d material z D s.val)
    (fun n xs u hu hc _ => body_executes input tape R material z D B d hfit htable hsize
      hcountlen s.val n xs origin u hu hc)
    count count.bits s (RationalAccumulator.address_bits count) hcounter hinit
  obtain ⟨_,finalIndex,hval,hlen,hms,hmwork,hmp,hmn,hf,hout⟩ := hm
  obtain ⟨t,et,htt,hg⟩ := WordCall.clear 136 input tape finalCount origin m hmc
  have keep (i : ℕ) (hi : i ≠ 136) : t.val.tapes i = m.val.tapes i := hg.2.2.2.2.2.1 i hi hi
  have htf : LoopFrame m.val t.val :=
    ⟨hg.2.1,hg.2.2.2.1,hg.2.2.2.2.1,fun i _ _ hi => keep i hi⟩
  refine ⟨a+(6*finalCount.length+4),t,finalIndex,?_,ea.seq et,by simpa using hval,hlen,
    hms.of_tapes (fun i hi => keep i ?_),workspace_of_tapes hmwork (fun i hi => keep i ?_),
    ⟨origin+finalCount.length,by simp [htt]⟩,?_,?_,hf.trans htf,
    hout.trans (OutputOutside.of_memory hg.2.2.1)⟩
  · simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_id] at hca
    dsimp [loopCost]
    rw [hmcl]
    dsimp only [count] at hca ⊢
    omega
  · rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro heq; subst i; exact (show 136 ∉ work by decide) hi
  · simpa only [hg.2.2.1,Nat.sub_zero,GenerationPrefix.complete] using hmp
  · simpa only [hg.2.2.1,Nat.sub_zero,GenerationPrefix.complete] using hmn

end Maxwell.Cost.CalibrationMatrix.Generation
