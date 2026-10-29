import Maxwell.Cost.CalibrationMatrix.GeneratedInitializer

namespace Maxwell.Cost.CalibrationMatrix.Generation
open Structured BankArray
open RationalAccumulator (Blank)
open Maxwell.Defect.FiniteStencil Maxwell.Spectral.Lattice

theorem init_run (input : List Bool) (tape : ℕ → Bool) (R : ℕ)
    (material : Cell20 → ℚ) (z : ℚ) (D B : ℕ) (d : Data R)
    (hfit : d.radix.length+d.dimension.length+((3*cubeWidth R^3)^2).bits.length+1 ≤ addressValue d.width)
    (htable : MaterialTable.outputBits 34 (MaterialEntry.table material z D) ≤ addressValue d.width)
    (hsize : d.Sized B) (hcountlen : ((3*cubeWidth R^3)^2).bits.length ≤ B)
    (index : List Bool) (hindex : addressValue index = 0)
    (hilen : index.length ≤ ((3*cubeWidth R^3)^2).bits.length)
    (origin : ℤ) (s : Store) (hs : Configured d index s.val) (hw : Workspace s.val)
    (h127 : Blank s.val 127)
    (hcounter : s.val.tapes 136 = BitTape.shifted ((3*cubeWidth R^3)^2).bits origin) :
    ∃ t : Store, ∃ finalIndex,
      (runPriced ((initCode material z D).compile.next input tape)
        (initCost R material z D B+1) s.val).finished = some (t.place (initCode material z D).size) ∧
      (runPriced ((initCode material z D).compile.next input tape)
        (initCost R material z D B+1) s.val).instructions ≤ initCost R material z D B ∧
      addressValue finalIndex = (3*cubeWidth R^3)^2 ∧
      finalIndex.length ≤ ((3*cubeWidth R^3)^2).bits.length ∧
      Stored d finalIndex t.val ∧ Workspace t.val ∧ Blank t.val 136 ∧
      BitArray.Represents t.val.memory (addressValue d.positiveBase) (addressValue d.width)
        (positiveWords R material z D (addressValue d.width)) ∧
      BitArray.Represents t.val.memory (addressValue d.negativeBase) (addressValue d.width)
        (negativeWords R material z D (addressValue d.width)) ∧
      InitFrame s.val t.val ∧
      OutputOutside d.output ((3*cubeWidth R^3)^2) (addressValue d.width) s.val t.val := by
  obtain ⟨cost,t,finalIndex,hcost,he,ht⟩ := init_executes input tape R material z D B d hfit
    htable hsize hcountlen index hindex hilen origin s hs hw h127 hcounter
  have hr := he.compiled_run (initCost R material z D B+1) (by omega)
  exact ⟨t,finalIndex,hr.1,hr.2.symm ▸ hcost,ht⟩

end Maxwell.Cost.CalibrationMatrix.Generation
