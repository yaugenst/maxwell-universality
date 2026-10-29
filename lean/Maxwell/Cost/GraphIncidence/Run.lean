import Maxwell.Cost.GraphIncidence.Pass

namespace Maxwell.Cost.GraphIncidence
open Structured
open BankArray (Word)
open RationalAccumulator (Blank)
open Maxwell.Logical.Routing

theorem run (width dimension count : ℕ) (clock : List Bool)
    (endpoint : Fin (4*count) → Fin (2*dimension+count))
    (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (numeric : PositiveGraph.Metadata.Numeric width dimension count s.val)
    (hclock : Word s.val 146 clock) (hclockLength : clock.length=width+3)
    (fresh : ∀ i, 600 ≤ i → i ≤ 612 → Blank s.val i)
    (scratch : BankArray.Scratch s.val) (h7 : Blank s.val 7)
    (hv : 2*dimension+count ≤ 2^(width+3)) (hd : IncidenceRanks.DegreeBound endpoint)
    (hrep : IncidenceEncoding.Represents (layout width dimension count) s.val.memory endpoint
      (IncidenceRanks.initial (2*dimension+count) (4*count))) :
    ∃ (t : Store) (index : List Bool),
      (runPriced (passCode.compile.next input tape) (passCost width dimension count clock+1) s.val).finished=
        some (t.place passCode.size) ∧
      (runPriced (passCode.compile.next input tape) (passCost width dimension count clock+1) s.val).instructions≤
        passCost width dimension count clock ∧
      addressValue index=4*count ∧ index.length≤(4*count).bits.length ∧
      IncidencePass.Config (layout width dimension count) index clock (t.renameTapes relocation.symm).val ∧
      IncidencePass.Workspace (t.renameTapes relocation.symm).val ∧ Blank t.val 612 ∧
      IncidenceEncoding.Represents (layout width dimension count) t.val.memory endpoint
        (IncidenceRanks.run endpoint (4*count) le_rfl) ∧
      SourceCircuit.Frame (Finset.Icc 600 612) s.val t.val ∧
      IncidencePass.MemoryFrame (layout width dimension count) (2*dimension+count) (4*count) s.val.memory t.val.memory := by
  obtain ⟨cost,t,index,hcost,he,ht⟩ := pass_executes width dimension count clock endpoint input tape s numeric hclock
    hclockLength fresh scratch h7 hv hd hrep
  have hr := he.compiled_run (passCost width dimension count clock+1) (by omega)
  exact ⟨t,index,hr.1,hr.2.symm ▸ hcost,ht⟩

end Maxwell.Cost.GraphIncidence
