import Maxwell.Cost.CalibrationSource.Producer

namespace Maxwell.Cost.CalibrationSource.Producer
open Structured CalibrationMatrix
open Defect.FiniteStencil Spectral.Lattice

/-- Actual priced execution, including the address arithmetic and the
mandatory source-width to calibration-width repacking. -/
theorem run {m : ℕ} (R0 L : ℕ) (v : Site) (edges : Fin m → Edge)
    (spacing degree B : ℕ) (c : Repack.Data) (base : List Bool) (d : ModeRead.Data m)
    (hc : c.Sized B) (hd : d.Sized B)
    (hsize : IndexArray.Sized R0 L spacing degree (indexData c base) B)
    (hm : m.bits.length ≤ B) (hlit : IndexArray.literalBudget R0 L v edges ≤ B)
    (he : ∀ i j, |(edges i).2 j| ≤ (R0 : ℤ)) (hv : ∀ j, |v j| ≤ (L : ℤ))
    (hwidth : (3*cubeWidth (radius R0 L spacing degree)^3).bits.length ≤ addressValue c.width)
    (hmodewidth : addressValue d.width ≤ addressValue c.width) (hsep : Separated c base d)
    (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hs : IndexArray.Stored R0 L spacing degree (indexData c base) s.val)
    (hb : ∀ a : Fin 2, BankArray.Word s.val (161+a.val) (c.bases a))
    (hmode : ModeRead.Stored Repack.readLayout d s.val)
    (hiwork : IndexArray.Workspace s.val) (hrwork : Repack.Workspace s.val) :
    ∃ t : Store,
      (runPriced ((code R0 L v edges).compile.next input tape) (costCap m B+1) s.val).finished =
        some (t.place (code R0 L v edges).size) ∧
      (runPriced ((code R0 L v edges).compile.next input tape) (costCap m B+1) s.val).instructions ≤ costCap m B ∧
      IndexArray.Stored R0 L spacing degree (indexData c base) t.val ∧
      BitArray.Represents t.val.memory (addressValue base) (addressValue c.width)
        (IndexArray.words R0 L v edges spacing degree (addressValue c.width)) ∧
      Repack.Stored c (Repack.words c d) t.val ∧ ModeRead.Stored Repack.readLayout d t.val ∧
      IndexArray.Workspace t.val ∧ Repack.Workspace t.val ∧ Frame s.val t.val ∧
      Outside c base m s.val t.val := by
  obtain ⟨cost,t,hcost,he,ht⟩ := executes R0 L v edges spacing degree B c base d hc hd hsize hm hlit
    he hv hwidth hmodewidth hsep input tape s hs hb hmode hiwork hrwork
  have hr := he.compiled_run (costCap m B+1) (by omega)
  exact ⟨t,hr.1,hr.2.symm ▸ hcost,ht⟩

theorem costCap_le (m B : ℕ) :
    costCap m B ≤ (m+1)*(4000*8^27+222002)*(B+2)^2 := by
  have hi := IndexArray.costCap_le m B
  have aux (x q a : ℕ) (hq : 1 ≤ q) :
      (x+1)*a*q+(1+x*(122000*q)) ≤ (x+1)*(a+122001)*q := by
    nlinarith only [hq,Nat.zero_le (x*q)]
  have hp : 1 ≤ (B+2)^2 := by
    have h : 0 < (B+2)^2 := by positivity
    omega
  dsimp only [costCap,Repack.costCap]
  exact (Nat.add_le_add_right hi _).trans (aux m ((B+2)^2) (4000*8^27+100001) hp)

end Maxwell.Cost.CalibrationSource.Producer
