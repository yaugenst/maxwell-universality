import Maxwell.Cost.CalibrationSource.IndexArray.Pass

namespace Maxwell.Cost.CalibrationSource.IndexArray
open Structured BankArray
open RationalAccumulator (Blank)
open Defect.FiniteStencil Spectral.Lattice

/-- A computable fixed-platform bound on every literal appearing in the
finite source-index program. It is independent of degree and spacing. -/
def literalBudget {m : ℕ} (R0 L : ℕ) (v : Site) (edges : Fin m → Edge) : ℕ :=
  Finset.univ.sup fun i => (indexInstructions R0 L v (edges i)).toFinset.sup NatAssign.Instruction.literalWidth

theorem literalWidth_le {m : ℕ} (R0 L : ℕ) (v : Site) (edges : Fin m → Edge)
    (i : Fin m) (a : NatAssign.Instruction) (ha : a ∈ indexInstructions R0 L v (edges i)) :
    a.literalWidth ≤ literalBudget R0 L v edges := by
  apply le_trans (Finset.le_sup (f := NatAssign.Instruction.literalWidth) (List.mem_toFinset.mpr ha))
  exact Finset.le_sup (f := fun i => (indexInstructions R0 L v (edges i)).toFinset.sup NatAssign.Instruction.literalWidth)
    (Finset.mem_univ i)

theorem address_bits_fit (R0 L : ℕ) (v : Site) (e : Edge) (d N W : ℕ)
    (he : ∀ j, |e.2 j| ≤ (R0 : ℤ)) (hv : ∀ j, |v j| ≤ (L : ℤ))
    (hw : (3*cubeWidth (radius R0 L d N)^3).bits.length ≤ W) :
    (address R0 L v e d N).bits.length ≤ W := by
  have h := Nat.size_le_size (Nat.le_of_lt (address_lt R0 L v e d N he hv))
  rw [← Nat.size_eq_bits_len,← Nat.size_eq_bits_len] at h
  exact h.trans hw

theorem represented_value {m : ℕ} (R0 L : ℕ) (v : Site) (edges : Fin m → Edge)
    (d N W base : ℕ) (memory : ℕ → Bool)
    (he : ∀ i j, |(edges i).2 j| ≤ (R0 : ℤ)) (hv : ∀ j, |v j| ≤ (L : ℤ))
    (hw : (3*cubeWidth (radius R0 L d N)^3).bits.length ≤ W)
    (harray : BitArray.Represents memory base W (words R0 L v edges d N W)) (i : Fin m) :
    addressValue (MemoryWord.readBits memory (base+i.val*W) W) = address R0 L v (edges i) d N := by
  rw [harray.read,words_get,FixedWidth.bits_value _ _ (address_bits_fit R0 L v (edges i) d N W (he i) hv hw),
    addressValue_bits]

/-- The produced memory indices are exactly the actual translated physical
source edges in the explicit cube enumeration. -/
theorem represented_edge {m : ℕ} (R0 L : ℕ) (v : Site) (edges : Fin m → Edge)
    (d N W base : ℕ) (memory : ℕ → Bool)
    (he : ∀ i j, |(edges i).2 j| ≤ (R0 : ℤ)) (hv : ∀ j, |v j| ≤ (L : ℤ))
    (hw : (3*cubeWidth (radius R0 L d N)^3).bits.length ≤ W)
    (harray : BitArray.Represents memory base W (words R0 L v edges d N W)) (i : Fin m) :
    ∃ index : Fin (3*cubeWidth (radius R0 L d N)^3),
      addressValue (MemoryWord.readBits memory (base+i.val*W) W) = index.val ∧
      radixCubeEmbedding (radius R0 L d N) index = Maxwell.Green.PhysicalCompression.translateEdge ((d : ℤ) • v) (edges i) := by
  refine ⟨⟨address R0 L v (edges i) d N,address_lt R0 L v (edges i) d N (he i) hv⟩,
    represented_value R0 L v edges d N W base memory he hv hw harray i,?_⟩
  exact address_edge R0 L v (edges i) d N (he i) hv

/-- The actual initializer needs only scalar descriptors and the fixed
support; arithmetic-fit premises follow from the physical support bounds. -/
theorem physical_executes {m : ℕ} (R0 L : ℕ) (v : Site) (edges : Fin m → Edge)
    (d N B : ℕ) (c : Data) (hsize : Sized R0 L d N c B) (hm : m.bits.length ≤ B)
    (hc : literalBudget R0 L v edges ≤ B)
    (he : ∀ i j, |(edges i).2 j| ≤ (R0 : ℤ)) (hv : ∀ j, |v j| ≤ (L : ℤ))
    (hwidth : (3*cubeWidth (radius R0 L d N)^3).bits.length ≤ addressValue c.width)
    (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hs : Stored R0 L d N c s.val) (hw : Workspace s.val) :
    ∃ cost t, cost ≤ costCap m B ∧ Executes input tape (code R0 L v edges) cost s t ∧
      Stored R0 L d N c t.val ∧ Workspace t.val ∧
      BitArray.Represents t.val.memory (addressValue c.base) (addressValue c.width)
        (words R0 L v edges d N (addressValue c.width)) ∧
      Frame s.val t.val ∧ Outside c m s.val t.val :=
  executes R0 L v edges d N B c hsize hm
    (fun i a ha => (literalWidth_le R0 L v edges i a ha).trans hc)
    (fun i => address_bits_fit R0 L v (edges i) d N (addressValue c.width) (he i) hv hwidth)
    input tape s hs hw

end Maxwell.Cost.CalibrationSource.IndexArray
