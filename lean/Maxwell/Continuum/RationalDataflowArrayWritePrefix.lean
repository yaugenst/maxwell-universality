import Maxwell.Continuum.RationalDataflowArrayOutput

/-! Indexed rational writes above a saved memory prefix preserve every
bit of that prefix, independently of the stored data's interpretation. -/
namespace Maxwell.Continuum.RationalDataflow.PartArray
open Maxwell.Cost

theorem Table.writeMemory_prefix {n : ℕ} (a : Table n) (i : Fin n) (x : Parts)
    (memory : ℕ→Bool) (limit : ℕ)
    (hp : limit ≤ addressValue a.basePositive) (hn : limit ≤ addressValue a.baseNegative)
    (hd : limit ≤ addressValue a.baseDenominator) (j : ℕ) (hj : j<limit) :
    a.writeMemory i x memory j=memory j := by
  unfold Table.writeMemory
  rw [MemoryWord.writeBits_outside _ _ _ _ (Or.inl (by omega)),
    MemoryWord.writeBits_outside _ _ _ _ (Or.inl (by omega)),
    MemoryWord.writeBits_outside _ _ _ _ (Or.inl (by omega))]

#print axioms Table.writeMemory_prefix
end Maxwell.Continuum.RationalDataflow.PartArray
