import Maxwell.Cost.GraphIncidence.Adapter
import Maxwell.Cost.GraphIncidence.Rename

namespace Maxwell.Cost.GraphIncidence
open Structured
open BankArray (Word)
open RationalAccumulator (Blank)

def privateCode : Code := .call (code.compile.renameTapes relocation)
def privatePrice (width dimension count : ℕ) (clock : List Bool) : ℕ :=
  price width dimension count clock (fun _ => [])+1

theorem private_frame {s t : Store}
    (h : SourceCircuit.Frame destinations.toFinset (s.renameTapes relocation.symm).val t.val) :
    SourceCircuit.Frame (Finset.Icc 600 612) s.val (t.renameTapes relocation).val := by
  refine ⟨h.inputHead,h.randomCursor,h.output,?_,h.sign,h.control⟩
  intro i hi hn
  have hs : shiftBank i=4 ∨ 10 ≤ shiftBank i := by
    dsimp only [shiftBank]
    split_ifs <;> omega
  have ho : shiftBank i∉destinations.toFinset := by
    simp only [Finset.mem_Icc,not_and_or] at hn
    simp only [List.mem_toFinset,destinations,List.mem_cons,List.not_mem_nil,or_false]
    dsimp only [shiftBank]
    split_ifs <;> omega
  have keep := h.tapes (shiftBank i) hs ho
  change t.val.tapes (shiftBank i)=s.val.tapes i
  simpa only [renamed_tape,shiftBank_involutive i] using keep

theorem virtual_scratch (s : Store) (h : BankArray.Scratch s.val) :
    BankArray.Scratch (s.renameTapes relocation.symm).val :=
  SourceCircuit.scratch_of_tapes h (fun i hi => by
    rw [renamed_tape,shiftBank_fixed i (by omega) (by omega)])

theorem virtual_sample (s : Store) (h : Blank s.val 7) :
    Blank (s.renameTapes relocation.symm).val 7 :=
  RationalAccumulator.blank_of_eq (by rw [renamed_tape]; rfl) h

/-- The public handoff uses only fresh tapes600–612. Source compiler archives
and all metadata outside that range retain their exact tapes and heads. -/
theorem prepares (width dimension count : ℕ) (clock : List Bool)
    (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (numeric : PositiveGraph.Metadata.Numeric width dimension count s.val)
    (hclock : Word s.val 146 clock)
    (fresh : ∀ i, 600 ≤ i → i ≤ 612 → Blank s.val i)
    (scratch : BankArray.Scratch s.val) (h7 : Blank s.val 7) :
    ∃ t : Store, Executes input tape privateCode (privatePrice width dimension count clock) s t ∧
      IncidencePass.Config (layout width dimension count) [] clock (t.renameTapes relocation.symm).val ∧
      IncidencePass.Workspace (t.renameTapes relocation.symm).val ∧
      Word t.val 612 (4*count).bits ∧ t.val.memory=s.val.memory ∧
      SourceCircuit.Frame (Finset.Icc 600 612) s.val t.val := by
  let v := s.renameTapes relocation.symm
  have old : WordAssign.Bank destinations v.val (fun _ => []) := by
    intro i hi
    have hlo : 80 ≤ i ∧ i ≤ 92 := by
      simp only [destinations,List.mem_cons,List.not_mem_nil,or_false] at hi
      omega
    obtain ⟨origin,ho⟩ := fresh (i+520) (by omega) (by omega)
    refine ⟨origin,?_⟩
    change s.val.tapes (shiftBank i)=_
    rw [shiftBank_old i hlo.1 hlo.2,ho]
    simp [BitTape.shifted,BitTape.blank]
  have vc : Word v.val 146 clock := BankArray.word_of_eq (by rw [renamed_tape]; rfl) hclock
  obtain ⟨a,ea,acfg,awork,a92,am,_,af⟩ := executes width dimension count clock (fun _ => []) input tape v
    (numeric_renamed width dimension count s numeric) vc old (virtual_scratch s scratch) (virtual_sample s h7)
  let t := a.renameTapes relocation
  have veq : t.renameTapes relocation.symm=a := by
    simpa only [t,Equiv.symm_symm] using Store.renameTapes_symm relocation.symm a
  refine ⟨t,?_,by rw [veq]; exact acfg,by rw [veq]; exact awork,?_,am,private_frame af⟩
  · simpa only [privateCode,privatePrice,v,Store.renameTapes_symm] using ea.renamed_call relocation
  · exact a92

end Maxwell.Cost.GraphIncidence
