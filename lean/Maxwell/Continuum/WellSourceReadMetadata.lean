import Maxwell.Continuum.RationalDataflowNaturalArrayRead
import Maxwell.Continuum.WellStrengthExecution

/-! Two charged metadata writes prepare the saved original-word reader.
The diagonal and incidence bases live on 993 and 994 and are never changed. -/
namespace Maxwell.Continuum.RationalDataflow.WellSourceRead
open Maxwell.Cost Maxwell.Cost.Structured
open RationalAccumulator (Word Blank)
set_option maxHeartbeats 2500000

def metaIds : Finset ℕ := {995,996}
def metaChanged : Finset ℕ := {0,1,2,3}∪metaIds
def prepare (width clock : ℕ) : List NatAssign.Instruction :=
  [.literal 995 width,.literal 996 clock]
def prepared (width clock : ℕ) (m : ℕ→ℕ) := NatAssign.values (prepare width clock) m

theorem prepare_valid (w c : ℕ) : ∀a∈prepare w c,a.Valid metaIds := by
  simp [prepare,NatAssign.Instruction.Valid,metaIds]

theorem prepared_width (w c : ℕ) (m : ℕ→ℕ) : prepared w c m 995=w := by
  simp [prepared,prepare,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,NatAssign.Instruction.value]
theorem prepared_clock (w c : ℕ) (m : ℕ→ℕ) : prepared w c m 996=c := by
  simp [prepared,prepare,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,NatAssign.Instruction.value]

theorem keep_rational {v : ℕ→Parts} {s t : Store}
    (hr : Ready WellStrength.bank v s) (f : BinaryPrecision.Frame metaChanged s.val t.val)
    (hz : NatAssign.Scratch t.val) : Ready WellStrength.bank v t := by
  refine ⟨?_,hz⟩
  intro i hi
  have hg := ids_ge_ten WellStrength.bank i hi
  have hout : i∉metaChanged := by
    intro h
    simp only [metaChanged,metaIds,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at h
    have hw : i∈workspace WellStrength.bank := Finset.mem_union_right _ hi
    rcases h with h | h
    · omega
    · rcases h with rfl | rfl
      · exact outside_workspace _ 995 (by decide) hw
      · exact outside_workspace _ 996 (by decide) hw
  exact RationalAccumulator.word_of_eq (f.tapes i hout) (hr.1 i hi)

theorem keep_scratch {s t : Store} (hs : BankArray.Scratch s.val)
    (f : BinaryPrecision.Frame metaChanged s.val t.val) (hz : NatAssign.Scratch t.val) :
    BankArray.Scratch t.val :=
  ⟨hz 0 (by decide),hz 1 (by decide),hz 2 (by decide),hz 3 (by decide),
   RationalAccumulator.blank_of_eq (f.tapes 5 (by decide)) hs.2.2.2.2.1,
   RationalAccumulator.blank_of_eq (f.tapes 6 (by decide)) hs.2.2.2.2.2.1,
   RationalAccumulator.blank_of_eq (f.tapes 8 (by decide)) hs.2.2.2.2.2.2.1,
   RationalAccumulator.blank_of_eq (f.tapes 9 (by decide)) hs.2.2.2.2.2.2.2⟩

theorem prepare_executes (w c B : ℕ) (hw : w.bits.length≤B) (hc : c.bits.length≤B)
    (v : ℕ→Parts) (m : ℕ→ℕ) (hm : ∀i∈metaIds,(m i).bits.length≤B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hr : Ready WellStrength.bank v s)
    (hs : BankArray.Scratch s.val) (h7 : Blank s.val 7)
    (hb : NatAssign.Bank metaIds m s.val) :
    ∃cost t,Executes input tape (NatAssign.code (prepare w c)) cost s t ∧ cost≤32*B+23 ∧
      Ready WellStrength.bank v t ∧ BankArray.Scratch t.val ∧ Blank t.val 7 ∧
      NatAssign.Bank metaIds (prepared w c m) t.val ∧
      BinaryPrecision.Frame metaChanged s.val t.val := by
  obtain ⟨cost,t,ex,hcost,bank,z,f⟩ := NatAssign.executes metaIds
    (by intro i hi;simp only [metaIds,Finset.mem_insert,Finset.mem_singleton] at hi;omega)
    (prepare w c) (prepare_valid w c) m input tape s hb hr.2
  have ff : BinaryPrecision.Frame metaChanged s.val t.val := f.mono (by
    simp [NatAssign.changes,prepare,NatAssign.Instruction.target,metaChanged,metaIds])
  refine ⟨cost,t,ex,?_,keep_rational hr ff z,keep_scratch hs ff z,
    RationalAccumulator.blank_of_eq (ff.tapes 7 (by decide)) h7,bank,ff⟩
  have h995 := hm 995 (by decide)
  have h996 := hm 996 (by decide)
  simp only [prepare,NatAssign.price,NatAssign.Instruction.price,NatAssign.Instruction.update,
    NatAssign.Instruction.target,NatAssign.Instruction.value,Function.update_of_ne (by decide : (996:ℕ)≠995)] at hcost
  omega

#print axioms prepare_executes
end Maxwell.Continuum.RationalDataflow.WellSourceRead
