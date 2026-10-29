import Maxwell.Cost.CalibrationMatrix.GenerationReady

namespace Maxwell.Cost.CalibrationMatrix.Generation
open Structured BankArray
open RationalAccumulator (Blank)
open Maxwell.Defect.FiniteStencil Maxwell.Spectral.Lattice
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

def cellCode (material : Cell20 → ℚ) (z : ℚ) (D : ℕ) : Code :=
  .seq (readyCode material z D) GeneratedWrite.code

def cellCost (material : Cell20 → ℚ) (z : ℚ) (D B : ℕ) : ℕ :=
  200000*(B+10)^2+MaterialEntry.costBound material z D

/-- One actual initialization iteration overwrites the two signed matrix
words and restores every private word for the next iteration. -/
theorem cell_executes (input : List Bool) (tape : ℕ → Bool) (R : ℕ)
    (material : Cell20 → ℚ) (z : ℚ) (D B : ℕ) (d : Data R)
    (i j : Fin (3*cubeWidth R^3)) (row : Fin ((3*cubeWidth R^3)^2))
    (hrow : row.val = i.val*(3*cubeWidth R^3)+j.val) (index : List Bool)
    (hindex : addressValue index = row.val)
    (hfit : d.radix.length+d.dimension.length+index.length+1 ≤ addressValue d.width)
    (htable : MaterialTable.outputBits 34 (MaterialEntry.table material z D) ≤ addressValue d.width)
    (hsize : d.Sized B) (hilen : index.length ≤ B)
    (positive negative : Vector (List Bool) ((3*cubeWidth R^3)^2))
    (s : Store) (hs : Stored d index s.val) (hb : Workspace s.val)
    (hp : BitArray.Represents s.val.memory (addressValue d.positiveBase) (addressValue d.width) positive)
    (hn : BitArray.Represents s.val.memory (addressValue d.negativeBase) (addressValue d.width) negative) :
    ∃ cost t, cost ≤ cellCost material z D B ∧
      Executes input tape (cellCode material z D) cost s t ∧
      Stored d index t.val ∧ Workspace t.val ∧
      t.val.memory = MemoryWord.writeBits
        (MemoryWord.writeBits s.val.memory (addressValue d.positiveBase+row.val*addressValue d.width)
          (FixedWidth.bits (addressValue d.width) ((matrix R material z D).positive i j).bits))
        (addressValue d.negativeBase+row.val*addressValue d.width)
          (FixedWidth.bits (addressValue d.width) ((matrix R material z D).negative i j).bits) ∧
      BitArray.Represents t.val.memory (addressValue d.positiveBase) (addressValue d.width)
        (positive.set row (FixedWidth.bits (addressValue d.width) ((matrix R material z D).positive i j).bits) (h := row.isLt)) ∧
      BitArray.Represents t.val.memory (addressValue d.negativeBase) (addressValue d.width)
        (negative.set row (FixedWidth.bits (addressValue d.width) ((matrix R material z D).negative i j).bits) (h := row.isLt)) ∧
      Frame s.val t.val := by
  obtain ⟨a,m,hca,ea,hmready,hmblank,hmm,hf⟩ := generate_ready input tape R material z D d i j index
    (hindex.trans hrow) hfit s hs hb
  have hms := hf.stored hs
  have hlength := MaterialEntry.channel_lengths material z D
    (entryKey (radixCubeEmbedding R i) (radixCubeEmbedding R j))
  rw [entryChannels_binding] at hlength
  change ((matrix R material z D).positive i j).bits.length+
    ((matrix R material z D).negative i j).bits.length ≤ _ at hlength
  obtain ⟨b,t,hcb,eb,htready,ht37,htm,htp,htn,hg⟩ := GeneratedWrite.executes input tape
    d.width index d.positiveBase d.negativeBase d.clock positive negative row
    ((matrix R material z D).positive i j) ((matrix R material z D).negative i j)
    d.width_nonempty hindex d.clock_length (by have := d.width_two; omega)
    (by omega) (by omega) d.separated m hmready (hmblank 37 (by decide) (by decide) (by decide))
    hms.width hms.index hms.positiveBase hms.negativeBase hms.clock
    (by simpa only [hmm] using hp) (by simpa only [hmm] using hn)
  have frame : Frame m.val t.val := by
    refine ⟨hg.1,hg.2.1,hg.2.2.1,?_⟩
    intro k hk
    have hh : k < 10 ∨ k = 30 ∨ k = 31 ∨ k = 37 → k ∈ work := by
      intro h
      have hsmall : Finset.range 10 ⊆ work := by decide
      rcases h with h | rfl | rfl | rfl
      · exact hsmall (by simp; omega)
      all_goals decide
    exact hg.2.2.2.1 k (Or.inr (by by_contra h; exact hk (hh (Or.inl (by omega)))))
      (by intro h; exact hk (hh (Or.inr (Or.inl h))))
      (by intro h; exact hk (hh (Or.inr (Or.inr (Or.inl h)))))
      (by intro h; exact hk (hh (Or.inr (Or.inr (Or.inr h)))))
  refine ⟨a+b,t,?_,ea.seq eb,frame.stored hms,
    workspace_of_write htready ht37 hg hmblank,?_,htp,htn,hf.trans frame⟩
  · obtain ⟨hw,hW,hr,hd,hp',hn'⟩ := hsize
    have hsum : d.radix.length+d.dimension.length+index.length+3 ≤ 3*B+3 := by omega
    have hsq := Nat.pow_le_pow_left hsum 2
    have hwq := Nat.pow_le_pow_left (show addressValue d.width+8 ≤ B+8 by omega) 2
    have hb' := hcb.trans (writeRow_cost_le d.width index d.positiveBase d.negativeBase
      ((matrix R material z D).positive i j) ((matrix R material z D).negative i j)
      B hw hilen hp' hn' hW)
    change a ≤ 5000*(d.radix.length+d.dimension.length+index.length+3)^2+
      (2100*(addressValue d.width+8)^2+3200+3500*(addressValue d.width+1)+410+
        MaterialEntry.costBound material z D+33*(6*addressValue d.width+4)+1) at hca
    change a+b ≤ 200000*(B+10)^2+MaterialEntry.costBound material z D
    nlinarith only [hca,hb',hsq,hwq,hW]
  · simpa only [hmm] using htm

end Maxwell.Cost.CalibrationMatrix.Generation
