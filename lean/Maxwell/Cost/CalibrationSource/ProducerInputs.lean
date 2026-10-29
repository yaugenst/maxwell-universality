import Maxwell.Cost.CalibrationSource.ProducerMeaning

namespace Maxwell.Cost.CalibrationSource.Producer
open Structured CalibrationMatrix
open Defect.FiniteStencil Spectral.Lattice
set_option maxHeartbeats 1000000

/-- Install the generated input-array evidence into the existing sparse
initializer contract. Output arrays may still contain arbitrary memory. -/
theorem produced_stored {m : ℕ} (R0 L : ℕ) (v : Site) (edges : Fin m → Edge) (spacing degree : ℕ)
    (c : Repack.Data) (base : List Bool) (d : ModeRead.Data m)
    (he : ∀ i j, |(edges i).2 j| ≤ (R0 : ℤ)) (hv : ∀ j, |v j| ≤ (L : ℤ))
    (hwidth : (3*cubeWidth (radius R0 L spacing degree)^3).bits.length ≤ addressValue c.width)
    (outputBases : Fin 4 → List Bool) (hout) (hin) (t : BitRAMState)
    (hi : IndexArray.Stored R0 L spacing degree (indexData c base) t)
    (hia : BitArray.Represents t.memory (addressValue base) (addressValue c.width)
      (IndexArray.words R0 L v edges spacing degree (addressValue c.width)))
    (hr : Repack.Stored c (Repack.words c d) t)
    (hdim : BankArray.Word t 107 (3*cubeWidth (radius R0 L spacing degree)^3).bits)
    (hcount : BankArray.Word t 159 m.bits)
    (houtputs : ∀ a : Fin 4, BankArray.Word t (120+a.val) (outputBases a)) :
    SourceInit.Stored (sourceData R0 L v edges spacing degree c base d he hv hwidth outputBases hout hin)
      (fun a => BitArray.snapshot t.memory (addressValue (outputBases a)) (addressValue c.width)
        (3*cubeWidth (radius R0 L spacing degree)^3)) t := by
  refine ⟨hi.width,hi.clock,hdim,hcount,?_,houtputs,?_,fun _ => BitArray.snapshot_represents _ _ _ _⟩
  · intro a
    fin_cases a
    · exact hi.base
    · exact hr.bases 0
    · exact hr.bases 1
  · intro a
    fin_cases a
    · exact hia
    · exact hr.arrays 0
    · exact hr.arrays 1

/-- The actual producer endpoint exposes the exact input object expected
by the zero/scatter/inverse pipeline, retaining the same qhat source. -/
theorem executes_inputs {m : ℕ} (R0 L : ℕ) (v : Site) (edges : Fin m → Edge)
    (spacing degree B : ℕ) (c : Repack.Data) (base : List Bool) (d : ModeRead.Data m)
    (hc : c.Sized B) (hd : d.Sized B)
    (hsize : IndexArray.Sized R0 L spacing degree (indexData c base) B)
    (hm : m.bits.length ≤ B) (hlit : IndexArray.literalBudget R0 L v edges ≤ B)
    (he : ∀ i j, |(edges i).2 j| ≤ (R0 : ℤ)) (hv : ∀ j, |v j| ≤ (L : ℤ))
    (hwidth : (3*cubeWidth (radius R0 L spacing degree)^3).bits.length ≤ addressValue c.width)
    (hmodewidth : addressValue d.width ≤ addressValue c.width) (hsep : Separated c base d)
    (outputBases : Fin 4 → List Bool) (hout) (hin)
    (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hs : IndexArray.Stored R0 L spacing degree (indexData c base) s.val)
    (hb : ∀ a : Fin 2, BankArray.Word s.val (161+a.val) (c.bases a))
    (hmode : ModeRead.Stored Repack.readLayout d s.val)
    (hiwork : IndexArray.Workspace s.val) (hrwork : Repack.Workspace s.val)
    (hdim : BankArray.Word s.val 107 (3*cubeWidth (radius R0 L spacing degree)^3).bits)
    (hcount : BankArray.Word s.val 159 m.bits)
    (houtputs : ∀ a : Fin 4, BankArray.Word s.val (120+a.val) (outputBases a)) :
    ∃ cost t, cost ≤ costCap m B ∧ Executes input tape (code R0 L v edges) cost s t ∧
      SourceInit.Stored (sourceData R0 L v edges spacing degree c base d he hv hwidth outputBases hout hin)
        (fun a => BitArray.snapshot t.val.memory (addressValue (outputBases a)) (addressValue c.width)
          (3*cubeWidth (radius R0 L spacing degree)^3)) t.val ∧
      ModeRead.Stored Repack.readLayout d t.val ∧ IndexArray.Workspace t.val ∧
      Repack.Workspace t.val ∧ Frame s.val t.val ∧ Outside c base m s.val t.val := by
  obtain ⟨cost,t,hcost,ex,ti,tia,tr,tm,tiw,trw,tf,tout⟩ := executes R0 L v edges spacing degree B c base d
    hc hd hsize hm hlit he hv hwidth hmodewidth hsep input tape s hs hb hmode hiwork hrwork
  have keep (j : ℕ) (hj : j = 107 ∨ j = 159 ∨ 120 ≤ j ∧ j ≤ 123) : t.val.tapes j = s.val.tapes j := by
    apply tf.tapes
    simp [work,IndexArray.work,IndexArray.cleanup]
    omega
  refine ⟨cost,t,hcost,ex,?_,tm,tiw,trw,tf,tout⟩
  apply produced_stored R0 L v edges spacing degree c base d he hv hwidth outputBases hout hin t.val ti tia tr
  · exact BankArray.word_of_eq (keep 107 (by omega)) hdim
  · exact BankArray.word_of_eq (keep 159 (by omega)) hcount
  · intro a
    exact BankArray.word_of_eq (keep _ (by omega)) (houtputs a)

end Maxwell.Cost.CalibrationSource.Producer
