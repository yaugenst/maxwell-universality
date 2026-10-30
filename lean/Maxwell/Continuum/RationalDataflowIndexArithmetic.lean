import Maxwell.Continuum.RationalDataflowArrayIndexRead
import Maxwell.Continuum.RationalDataflowArrayFrame

/-! Fixed-stride row indices are computed by literal Boolean instructions.
The outer padded countdown word is cloned and remains exactly unchanged. -/

namespace Maxwell.Continuum.RationalDataflow.PartArray.RowIndex
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

def cloneCanonicalCode (source target : ℕ) : Code :=
  .seq (.call (WordTransfer.clone source target)) (.call (NormalizeWord.program target))

theorem cloneCanonical_executes (source target : ℕ) (hne : source≠target)
    (input : List Bool) (tape : ℕ→Bool) (word : List Bool) (s : Store)
    (hs : BankArray.Word s.val source word) (ht : RationalAccumulator.Blank s.val target) :
    ∃ cost t, Executes input tape (cloneCanonicalCode source target) cost s t ∧
      cost≤31*word.length+35 ∧ RationalAccumulator.Word t.val target (addressValue word) ∧
      BinaryPrecision.Frame {target} s.val t.val := by
  obtain ⟨so,hso⟩ := hs
  obtain ⟨targetOrigin,hto⟩ := ht
  obtain ⟨r,er,htr,fr⟩ := WordCall.clone source target hne input tape word so targetOrigin s hso hto
  have hword : r.val.tapes target=BitTape.shifted word targetOrigin := by simp only [htr,Function.update_self]
  obtain ⟨cn,t,hcn,en,hpc,hwt,_,fn⟩ := NormalizeWord.simulation target targetOrigin input tape word r.val r.property hword
  have en' : Executes input tape (.call (NormalizeWord.program target)) (cn+1) r (Store.ofState t) :=
    .call _ r t _ en (by simp [NormalizeWord.program,hpc,ScanForward.program,TapeOps.trim,
      Rewind.program,BitRAMInstruction.relocate])
  refine ⟨(15*word.length+17)+(cn+1),Store.ofState t,er.seq en',by omega,⟨targetOrigin,hwt⟩,?_⟩
  refine ⟨fn.1.trans fr.1,fn.2.1.trans fr.2.1,fn.2.2.1.trans fr.2.2.1,
    fn.2.2.2.1.trans fr.2.2.2.1,fn.2.2.2.2.1.trans fr.2.2.2.2.1,?_⟩
  intro i hi
  have hit : i≠target := by simpa only [Finset.mem_singleton] using hi
  exact (fn.2.2.2.2.2.1 i hit).trans (by simp only [htr,Function.update_of_ne hit])

def ids : Finset ℕ := {220,221,222}

def instructions (stride offset : ℕ) : List NatAssign.Instruction :=
  [.literal 221 stride,.multiply 220 221,.literal 222 offset,.add 222 221]

def initial (row : ℕ) : ℕ→ℕ := fun i => if i=220 then row else 0

def values (stride offset row : ℕ) : ℕ→ℕ :=
  fun i => if i=220 then row else if i=221 then stride*row+offset else if i=222 then offset else 0

def changed : Finset ℕ := {0,1,2,3,220,221,222}

def code (stride offset : ℕ) : Code :=
  .seq (cloneCanonicalCode 201 220) (NatAssign.code (instructions stride offset))

theorem instructions_valid (stride offset : ℕ) :
    ∀a∈instructions stride offset,a.Valid ids := by
  simp [instructions,NatAssign.Instruction.Valid,ids]

theorem instructions_values (stride offset row : ℕ) :
    NatAssign.values (instructions stride offset) (initial row)=values stride offset row := by
  funext i
  simp only [instructions,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,NatAssign.Instruction.value]
  by_cases h0 : i=220
  · subst i; simp [initial,values]
  by_cases h1 : i=221
  · subst i; simp [initial,values,Nat.mul_comm,Nat.add_comm]
  by_cases h2 : i=222
  · subst i; simp [initial,values]
  simp [initial,values,h0,h1,h2]

theorem instruction_price (stride offset row : ℕ) :
    NatAssign.price (instructions stride offset) (initial row)≤
      2^20*(row.bits.length+stride.bits.length+offset.bits.length+5)^2 := by
  have hm := RationalAccumulator.bits_mul_le row stride
  simp [instructions,NatAssign.price,NatAssign.Instruction.price,
    NatAssign.Instruction.update,NatAssign.Instruction.target,NatAssign.Instruction.value,
    initial]
  nlinarith only [hm,Nat.zero_le row.bits.length,Nat.zero_le stride.bits.length,
    Nat.zero_le offset.bits.length]

theorem executes (stride offset : ℕ) (input : List Bool) (tape : ℕ→Bool)
    (word : List Bool) (s : Store) (hindex : BankArray.Word s.val 201 word)
    (hblank : ∀i∈ids,RationalAccumulator.Blank s.val i) (hs : NatAssign.Scratch s.val) :
    ∃ cost t, Executes input tape (code stride offset) cost s t ∧
      cost≤2^22*(word.length+stride.bits.length+offset.bits.length+5)^2 ∧
      NatAssign.Bank ids (values stride offset (addressValue word)) t.val ∧
      NatAssign.Scratch t.val ∧ BinaryPrecision.Frame changed s.val t.val := by
  obtain ⟨cc,r,ec,hcc,hword,fc⟩ := cloneCanonical_executes 201 220 (by decide) input tape word s
    hindex (hblank 220 (by simp [ids]))
  have hr : NatAssign.Bank ids (initial (addressValue word)) r.val := by
    intro i hi
    simp only [ids,Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · simpa only [initial,ite_true] using hword
    · have hh := RationalAccumulator.blank_of_eq (fc.tapes 221 (by decide))
        (hblank 221 (by simp [ids]))
      simpa [initial] using
        (RationalAccumulator.zero_word_iff_blank _ _).mpr hh
    · have hh := RationalAccumulator.blank_of_eq (fc.tapes 222 (by decide))
        (hblank 222 (by simp [ids]))
      simpa [initial] using
        (RationalAccumulator.zero_word_iff_blank _ _).mpr hh
  have hz : NatAssign.Scratch r.val := fun i hi =>
    RationalAccumulator.blank_of_eq (fc.tapes i (by simp only [Finset.mem_singleton];omega)) (hs i hi)
  obtain ⟨ca,t,ea,hca,hbank,hsc,fa⟩ := NatAssign.executes ids
    (by intro i hi; simp only [ids,Finset.mem_insert,Finset.mem_singleton] at hi; omega)
    (instructions stride offset) (instructions_valid stride offset)
    (initial (addressValue word)) input tape r hr hz
  refine ⟨cc+ca,t,ec.seq ea,?_,?_,hsc,?_⟩
  · have hb : (addressValue word).bits.length≤word.length := by
      rw [Nat.size_eq_bits_len]
      exact Nat.size_le.mpr (Subtraction.addressValue_lt_pow_length word)
    have hp := (instruction_price stride offset (addressValue word)).trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega :
        (addressValue word).bits.length+stride.bits.length+offset.bits.length+5≤
          word.length+stride.bits.length+offset.bits.length+5) 2))
    nlinarith only [hcc,hca,hp,Nat.zero_le word.length,Nat.zero_le stride.bits.length,
      Nat.zero_le offset.bits.length]
  · simpa only [instructions_values] using hbank
  · exact (fc.mono (by simp [changed])).trans (fa.mono (by
      intro i hi
      simp only [NatAssign.changes,instructions,NatAssign.Instruction.target,List.map_cons,
        List.map_nil,List.toFinset_cons,List.toFinset_nil,Finset.mem_union,
        Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,changed] at hi ⊢
      tauto))

#print axioms cloneCanonical_executes
#print axioms executes
end Maxwell.Continuum.RationalDataflow.PartArray.RowIndex
