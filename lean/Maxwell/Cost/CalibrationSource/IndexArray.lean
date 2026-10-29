import Maxwell.Cost.CalibrationSource.IndexArray.Physical
import Maxwell.Cost.CalibrationSource.IndexArray.Cost

namespace Maxwell.Cost.CalibrationSource.IndexArray
open Structured BankArray
open Defect.FiniteStencil Spectral.Lattice

theorem run {m : ℕ} (R0 L : ℕ) (v : Site) (edges : Fin m → Edge)
    (d N B : ℕ) (c : Data) (hsize : Sized R0 L d N c B) (hm : m.bits.length ≤ B)
    (hc : literalBudget R0 L v edges ≤ B)
    (he : ∀ i j, |(edges i).2 j| ≤ (R0 : ℤ)) (hv : ∀ j, |v j| ≤ (L : ℤ))
    (hwidth : (3*cubeWidth (radius R0 L d N)^3).bits.length ≤ addressValue c.width)
    (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hs : Stored R0 L d N c s.val) (hw : Workspace s.val) :
    ∃ t : Store,
      (runPriced ((code R0 L v edges).compile.next input tape) (costCap m B+1) s.val).finished =
        some (t.place (code R0 L v edges).size) ∧
      (runPriced ((code R0 L v edges).compile.next input tape) (costCap m B+1) s.val).instructions ≤ costCap m B ∧
      Stored R0 L d N c t.val ∧ Workspace t.val ∧
      BitArray.Represents t.val.memory (addressValue c.base) (addressValue c.width)
        (words R0 L v edges d N (addressValue c.width)) ∧
      Frame s.val t.val ∧ Outside c m s.val t.val := by
  obtain ⟨cost,t,hcost,he,ht⟩ := physical_executes R0 L v edges d N B c hsize hm hc he hv hwidth
    input tape s hs hw
  have hr := he.compiled_run (costCap m B+1) (by omega)
  exact ⟨t,hr.1,hr.2.symm ▸ hcost,ht⟩

end Maxwell.Cost.CalibrationSource.IndexArray
