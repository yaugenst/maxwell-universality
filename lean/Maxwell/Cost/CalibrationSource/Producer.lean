import Maxwell.Cost.CalibrationSource.ProducerData

namespace Maxwell.Cost.CalibrationSource.Producer
open Structured CalibrationMatrix
open RationalAccumulator (Blank)
open Defect.FiniteStencil Spectral.Lattice
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

def code {m : ℕ} (R0 L : ℕ) (v : Site) (edges : Fin m → Edge) : Code :=
  .seq (IndexArray.code R0 L v edges) (Repack.code m)

def costCap (m B : ℕ) : ℕ := IndexArray.costCap m B+Repack.costCap m B

/-- Produce all three sparse record arrays by actual arithmetic, indexed
reads and writes. Initial sparse-array memory is unrestricted. -/
theorem executes {m : ℕ} (R0 L : ℕ) (v : Site) (edges : Fin m → Edge)
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
    ∃ cost t, cost ≤ costCap m B ∧ Executes input tape (code R0 L v edges) cost s t ∧
      IndexArray.Stored R0 L spacing degree (indexData c base) t.val ∧
      BitArray.Represents t.val.memory (addressValue base) (addressValue c.width)
        (IndexArray.words R0 L v edges spacing degree (addressValue c.width)) ∧
      Repack.Stored c (Repack.words c d) t.val ∧ ModeRead.Stored Repack.readLayout d t.val ∧
      IndexArray.Workspace t.val ∧ Repack.Workspace t.val ∧ Frame s.val t.val ∧
      Outside c base m s.val t.val := by
  obtain ⟨ic,a,hic,ei,ast,aw,ai,af,ao⟩ := IndexArray.physical_executes R0 L v edges spacing degree B
    (indexData c base) hsize hm hlit he hv hwidth input tape s hs hiwork
  have amode := modeStored_after_index hmode af ao hsep.mode_index
  have ar : Repack.Workspace a.val := by
    refine ⟨⟨?_,aw.scratch,aw 7 (by decide)⟩,aw 4 (by decide),aw 37 (by decide),?_⟩
    · intro j hj hj'
      exact RationalAccumulator.word_of_eq (af.tapes j (by
        simp [IndexArray.work,IndexArray.cleanup]
        omega)) (hrwork.1.1 j hj hj')
    · exact RationalAccumulator.blank_of_eq (af.tapes 104 (by decide)) hrwork.2.2.2
  have abase (j : Fin 2) : BankArray.Word a.val (161+j.val) (c.bases j) := by
    apply BankArray.word_of_eq (af.tapes _ _) (hb j)
    fin_cases j <;> decide
  obtain ⟨rc,t,hrc,er,tr,tm,tw,tf,tout⟩ := Repack.executes c d B hc hd hsep.coefficients
    hmodewidth hm input tape a ast.width ast.clock abase amode ar
  have tindex := ast.of_tapes (by
    intro j hj
    exact tf.tapes j (by omega) (by omega) (by omega) (by omega) (by omega))
  have tiwork : IndexArray.Workspace t.val := by
    intro j hj
    by_cases hlow : j < 10
    · exact Repack.modeReady tw.1 tw.2.1 j hlow
    by_cases h37 : j = 37
    · subst j; exact tw.2.2.1
    apply RationalAccumulator.blank_of_eq (tf.tapes j (by omega) ?_ ?_ h37 ?_) (aw j hj)
    all_goals
      simp [IndexArray.work,IndexArray.cleanup] at hj
      omega
  have frame : Frame s.val t.val := by
    refine ⟨tf.inputHead.trans af.inputHead,tf.randomCursor.trans af.randomCursor,
      tf.output.trans af.output,?_⟩
    intro j hj
    have hi : j ∉ IndexArray.work := fun h => hj (Finset.mem_union_left _ h)
    have hrest : j ∉ ({30,31,32,33,34,35,36,104} : Finset ℕ) :=
      fun h => hj (Finset.mem_union_right _ h)
    have h37 : j ≠ 37 := by intro h; subst j; exact hi (by decide)
    have hlow : 10 ≤ j := by
      by_contra h
      exact hi (by simp [IndexArray.work];omega)
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hrest
    exact (tf.tapes j (Or.inr hlow) (by tauto) (by tauto) h37 (by tauto)).trans (af.tapes j hi)
  refine ⟨ic+rc,t,Nat.add_le_add hic hrc,ei.seq er,tindex,
    represents_after_repack ai tout hsep.index_coefficients,tr,tm,tiwork,tw,frame,?_⟩
  intro address hi hp hn
  exact (tout address hp hn).trans (ao address hi)

end Maxwell.Cost.CalibrationSource.Producer
