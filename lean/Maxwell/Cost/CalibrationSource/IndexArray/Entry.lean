import Maxwell.Cost.CalibrationSource.IndexArray.State
import Maxwell.Cost.CalibrationMatrix.Rows

namespace Maxwell.Cost.CalibrationSource.IndexArray
open Structured BankArray
open RationalAccumulator (Blank)
open Defect.FiniteStencil Spectral.Lattice
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

def entryCode (R0 L : ℕ) (v : Site) (e : Edge) (row : ℕ) : Code :=
  .seq (BinaryPrecision.literalCode 102 row)
    (.seq (indexCode R0 L v e)
      (.seq (writeCanonicalCode 100 102 160 101 285) (CalibrationMatrix.EraseWords.code cleanup)))

def entryCost (B : ℕ) : ℕ :=
  10*B+7+(3000*8^27*(B+2)^2+(80000*(B+2)^2+7*(6*(2^27*(B+1))+4)+1))

/-- Compute one translated source index, write its actual fixed-width
array word, and reclaim the literal cursor and every arithmetic temporary. -/
theorem entry_executes {m : ℕ} (R0 L : ℕ) (v : Site) (e : Edge) (d N B : ℕ)
    (c : Data) (row : Fin m) (hrow : row.val.bits.length ≤ B)
    (hsize : Sized R0 L d N c B)
    (hc : ∀ a ∈ indexInstructions R0 L v e, a.literalWidth ≤ B)
    (hfit : (address R0 L v e d N).bits.length ≤ addressValue c.width)
    (words : Vector (List Bool) m) (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hs : Stored R0 L d N c s.val) (hw : Workspace s.val)
    (ha : BitArray.Represents s.val.memory (addressValue c.base) (addressValue c.width) words) :
    ∃ cost t, cost ≤ entryCost B ∧ Executes input tape (entryCode R0 L v e row.val) cost s t ∧
      Stored R0 L d N c t.val ∧ Workspace t.val ∧
      t.val.memory = MemoryWord.writeBits s.val.memory
        (addressValue c.base+row.val*addressValue c.width)
        (FixedWidth.bits (addressValue c.width) (address R0 L v e d N).bits) ∧
      BitArray.Represents t.val.memory (addressValue c.base) (addressValue c.width)
        (words.set row (FixedWidth.bits (addressValue c.width) (address R0 L v e d N).bits) (h := row.isLt)) ∧
      Frame s.val t.val := by
  let values := initial N d (cubeWidth (radius R0 L d N))
  have hbank := stored_initial hs hw
  obtain ⟨a,ea,ha102,fa⟩ := BinaryPrecision.literal 102 row.val input tape s (hw 102 (by decide))
  have havals : NatAssign.Bank indexIds values a.val := by
    intro i hi
    apply RationalAccumulator.word_of_eq (fa.tapes i ?_) (hbank i hi)
    have hh : 102 ∉ indexIds := by decide
    simpa using (show i ≠ 102 by intro heq; subst i; exact hh hi)
  have hsource : NatAssign.Scratch a.val := fun i hi =>
    fa.blank (by simp; omega) (hw i (by simp [work]; omega))
  obtain ⟨b,p,eb,hcb,hp285,hpbank,hpscratch,fb⟩ := index_executes R0 L v e d N B values
    (by simp [values,initial]) (by simp [values,initial]) (by simp [values,initial])
    (initial_width hsize) hc input tape a havals hsource
  have fbp := fb.mono (index_changes R0 L v e)
  have pblank (i : ℕ) (hi : i < 10 ∨ i = 37) : Blank p.val i := by
    by_cases hl : i < 4
    · exact hpscratch i hl
    apply fbp.blank (by simp [indexWork]; omega)
    apply fa.blank (by simp; omega)
    exact hw i (by simp [work]; omega)
  have pscratch : Scratch p.val := ⟨pblank 0 (by omega),pblank 1 (by omega),pblank 2 (by omega),
    pblank 3 (by omega),pblank 5 (by omega),pblank 6 (by omega),pblank 8 (by omega),pblank 9 (by omega)⟩
  have ps : Stored R0 L d N c p.val := hs.of_tapes (by
    intro i hi
    exact (fbp.tapes i (by rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)).trans
      (fa.tapes i (by rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)))
  have pi : Word p.val 102 row.val.bits := by
    apply fbp.word (by decide)
    exact ha102
  have pmemory : p.val.memory = s.val.memory := fb.memory.trans fa.memory
  obtain ⟨w,q,hwcost,ew,hqm,hqarray,hqs,hq7,hq37,fq⟩ := write_canonical 100 102 160 101 285
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    input tape c.width row.val.bits c.base c.clock words row (address R0 L v e d N)
    c.width_nonempty (addressValue_bits row.val) c.clock_length c.width_positive hfit p pscratch
    (pblank 7 (by omega)) (pblank 37 (by omega)) ps.width pi ps.base ps.clock hp285
    (by simpa only [pmemory] using ha)
  let result := NatAssign.values (indexInstructions R0 L v e) values
  let clearWords := fun i => if i=102 then row.val.bits else (result i).bits
  have hwidths := values_width indexIds (indexInstructions R0 L v e)
    (indexInstructions_valid R0 L v e) values B (initial_width hsize) hc
  rw [indexInstructions_length] at hwidths
  have clearLength : ∀ i ∈ cleanup, (clearWords i).length ≤ 2^27*(B+1) := by
    intro i hi
    by_cases h102 : i=102
    · simp only [clearWords,h102,ite_true]
      have hpow : 1 ≤ 2^27 := by decide
      have hmul := Nat.mul_le_mul_right (B+1) hpow
      omega
    · simp only [clearWords,h102,ite_false]
      exact hwidths i (by
        have hh : cleanup.toFinset \ {102} ⊆ indexIds := by decide
        exact hh (by simp [hi,h102]))
  have clearStored : ∀ i ∈ cleanup, Word q.val i (clearWords i) := by
    intro i hi
    have hlarge : 100 ≤ i := by simp only [cleanup,List.mem_cons,List.not_mem_nil,or_false] at hi; omega
    apply word_of_eq (fq.2.2.2.1 i (Or.inr (by omega)) (by omega))
    by_cases h102 : i=102
    · subst i
      simpa only [clearWords,ite_true] using pi
    · simp only [clearWords,h102,ite_false]
      exact hpbank i (by
        have hh : cleanup.toFinset \ {102} ⊆ indexIds := by decide
        exact hh (by simp [hi,h102]))
  obtain ⟨x,t,hcx,ex,htblank,fx⟩ := CalibrationMatrix.EraseWords.executes cleanup
    (2^27*(B+1)) clearWords clearLength input tape q clearStored
  have finalBlank (i : ℕ) (hi : i < 10 ∨ i = 37) : Blank t.val i := by
    apply fx.blank (by simp [cleanup]; omega)
    by_cases h37 : i=37
    · subst i; exact hq37
    have hl : i < 10 := by omega
    interval_cases i
    · exact hqs.1
    · exact hqs.2.1
    · exact hqs.2.2.1
    · exact hqs.2.2.2.1
    · exact RationalAccumulator.blank_of_eq (fq.2.2.2.1 4 (by omega) (by omega)) (pblank 4 (by omega))
    · exact hqs.2.2.2.2.1
    · exact hqs.2.2.2.2.2.1
    · exact hq7
    · exact hqs.2.2.2.2.2.2.1
    · exact hqs.2.2.2.2.2.2.2
  have frame : Frame s.val t.val := by
    refine ⟨fx.inputHead.trans (fq.1.trans (fb.inputHead.trans fa.inputHead)),
      fx.randomCursor.trans (fq.2.1.trans (fb.randomCursor.trans fa.randomCursor)),
      fx.output.trans (fq.2.2.1.trans (fb.output.trans fa.output)),?_⟩
    intro i hi
    have hclean : i ∉ cleanup.toFinset := fun hin => hi (Finset.mem_union_right _ hin)
    have hlow : 10 ≤ i := by
      by_contra h
      exact hi (Finset.mem_union_left _ (Finset.mem_union_left _ (by simp; omega)))
    have h37 : i ≠ 37 := by intro heq; subst i; exact hi (by decide)
    have h102 : i ≠ 102 := by intro heq; subst i; exact hi (by decide)
    have hidx : i ∉ indexWork := by
      have hh : indexWork ⊆ work := by decide
      exact fun hin => hi (hh hin)
    exact (fx.tapes i hclean).trans ((fq.2.2.2.1 i (Or.inr hlow) h37).trans
      ((fbp.tapes i hidx).trans (fa.tapes i (by simpa using h102))))
  refine ⟨10*row.val.bits.length+7+(b+(w+x)),t,?_,ea.seq (eb.seq (ew.seq ex)),frame.stored hs,?_,?_,?_,frame⟩
  · have hcwrite := CalibrationMatrix.writeRow_cost_le c.width row.val.bits c.base c.base
      (address R0 L v e d N) 0 B hsize.1 hrow hsize.2.2.1 hsize.2.2.1 hsize.2.1
    have hwbound : w ≤ 80000*(B+2)^2 := by omega
    have hcleanup : cleanup.length = 7 := rfl
    rw [hcleanup] at hcx
    dsimp only [entryCost]
    omega
  · intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · rcases Finset.mem_union.mp hi with hi | hi
      · exact finalBlank i (Or.inl (Finset.mem_range.mp hi))
      · exact finalBlank i (Or.inr (by simpa using hi))
    · exact htblank i (List.mem_toFinset.mp hi)
  · rw [fx.memory,hqm,pmemory]
  · simpa only [fx.memory] using hqarray

end Maxwell.Cost.CalibrationSource.IndexArray
