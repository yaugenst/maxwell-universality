import Maxwell.Cost.GraphIncidence.Fresh

namespace Maxwell.Cost.GraphIncidence
open Structured
open BankArray (Word)
open RationalAccumulator (Blank)
open Maxwell.Logical.Routing

def passCode : Code := .seq privateCode (.call (IncidencePass.loopCode.compile.renameTapes relocation))
def passCost (width dimension count : ℕ) (clock : List Bool) : ℕ :=
  privatePrice width dimension count clock+IncidencePass.loopCost (layout width dimension count) (4*count)+1

theorem loop_private_frame {s t : Store} (h : IncidencePass.LoopFrame (s.renameTapes relocation.symm).val t.val) :
    SourceCircuit.Frame (Finset.Icc 600 612) s.val (t.renameTapes relocation).val := by
  refine ⟨h.1,h.2.1,h.2.2.1,?_,?_,?_⟩
  · intro i hi hn
    have hs : shiftBank i=4 ∨ 10 ≤ shiftBank i := by
      dsimp only [shiftBank]
      split_ifs <;> omega
    have ho : ¬(80 ≤ shiftBank i ∧ shiftBank i ≤ 92) := by
      simp only [Finset.mem_Icc,not_and_or] at hn
      dsimp only [shiftBank]
      split_ifs <;> omega
    have keep := h.2.2.2.1 (shiftBank i) hs (by omega) (by omega) (by omega) (by omega) (by omega)
    change t.val.tapes (shiftBank i)=s.val.tapes i
    simpa only [renamed_tape,shiftBank_involutive i] using keep
  · exact h.2.2.2.2 23 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  · intro i hi
    exact h.2.2.2.2 i (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

/-- Execute the complete incidence pass directly from the graph handoff.
Only fresh600–612 and the two counter/rank memory intervals change. -/
theorem pass_executes (width dimension count : ℕ) (clock : List Bool)
    (endpoint : Fin (4*count) → Fin (2*dimension+count))
    (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (numeric : PositiveGraph.Metadata.Numeric width dimension count s.val)
    (hclock : Word s.val 146 clock) (hclockLength : clock.length=width+3)
    (fresh : ∀ i, 600 ≤ i → i ≤ 612 → Blank s.val i)
    (scratch : BankArray.Scratch s.val) (h7 : Blank s.val 7)
    (hv : 2*dimension+count ≤ 2^(width+3)) (hd : IncidenceRanks.DegreeBound endpoint)
    (hrep : IncidenceEncoding.Represents (layout width dimension count) s.val.memory endpoint
      (IncidenceRanks.initial (2*dimension+count) (4*count))) :
    ∃ cost t index, cost≤passCost width dimension count clock ∧ Executes input tape passCode cost s t ∧
      addressValue index=4*count ∧ index.length≤(4*count).bits.length ∧
      IncidencePass.Config (layout width dimension count) index clock (t.renameTapes relocation.symm).val ∧
      IncidencePass.Workspace (t.renameTapes relocation.symm).val ∧ Blank t.val 612 ∧
      IncidenceEncoding.Represents (layout width dimension count) t.val.memory endpoint
        (IncidenceRanks.run endpoint (4*count) le_rfl) ∧
      SourceCircuit.Frame (Finset.Icc 600 612) s.val t.val ∧
      IncidencePass.MemoryFrame (layout width dimension count) (2*dimension+count) (4*count) s.val.memory t.val.memory := by
  obtain ⟨a,ea,acfg,awork,a92,am,af⟩ := prepares width dimension count clock input tape s numeric hclock fresh scratch h7
  obtain ⟨co,a92⟩ := a92
  have hsep : (layout width dimension count).Separated (2*dimension+count) (4*count) := by
    simpa only [layout,IncidenceEncoding.Layout.packed,Nat.mul_comm] using
      IncidenceEncoding.Layout.packed_separated (2*dimension+count) (4*count) (width+3)
  obtain ⟨cost,v,index,hcost,ev,hindex,hlen,vcfg,vwork,v92,vrep,vf,vm⟩ :=
    IncidencePass.loop_executes input tape (layout width dimension count) endpoint [] clock
      (by dsimp [layout]; omega) hv hclockLength hsep hd rfl (by simp)
      co (a.renameTapes relocation.symm) a92 acfg awork (by simpa only [Store.renameTapes,BitRAMState.renameTapes,am] using hrep)
  let t := v.renameTapes relocation
  have veq : t.renameTapes relocation.symm=v := by
    simpa only [t,Equiv.symm_symm] using Store.renameTapes_symm relocation.symm v
  refine ⟨privatePrice width dimension count clock+(cost+1),t,index,by dsimp [passCost]; omega,
    ea.seq ?_,hindex,hlen,by rw [veq]; exact vcfg,by rw [veq]; exact vwork,v92,vrep,
    af.trans (loop_private_frame vf),?_⟩
  · simpa only [Store.renameTapes_symm] using ev.renamed_call relocation
  · exact (IncidencePass.MemoryFrame.of_eq am).trans vm

end Maxwell.Cost.GraphIncidence
