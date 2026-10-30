import Maxwell.Continuum.StoredGeometryRead

/-! Actual cursor advancement after each packed geometry read. The source
array remains unchanged, and both enclosing runtime counters are preserved. -/
namespace Maxwell.Continuum.GeometryOutput
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 2500000
set_option maxRecDepth 16384

def readAdvanceCode (target : ℕ) : Code :=
  .seq (readCode target) (NatAssign.Instruction.add 970 971).code

def readAdvanceValues (v : ℕ→ℕ) (target value : ℕ) : ℕ→ℕ :=
  Function.update (Function.update v target value) 971 (v 971+1)

structure ReadFrame (work : Finset ℕ) (s t : BitRAMState) : Prop where
  memory : t.memory=s.memory
  inputHead : t.inputHead=s.inputHead
  randomCursor : t.randomCursor=s.randomCursor
  output : t.output=s.output
  tapes : ∀i,10 ≤ i → i∉work→t.tapes i=s.tapes i

theorem readAdvance_executes {n : ℕ} (values : Vector ℕ n) (base width B : ℕ) (clock : List Bool)
    (hwidth : 0<width) (hwidthB : width≤B) (hlen : clock.length=width) (hn : n.bits.length≤B)
    (target : ℕ) (ht : target∈ids) (ht₀ : target≠960) (ht₁ : target≠961) (ht₂ : target≠962)
    (hti : target≠971) (hto : target≠970) (v : ℕ→ℕ) (hv : ∀i∈ids,(v i).bits.length≤B)
    (hbase : v 960=base) (hwidthv : v 961=width) (i : Fin n) (hindex : v 971=i.val) (hone : v 970=1)
    (hfit : (values.get i).bits.length≤width)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : Ready v s)
    (hclock : BankArray.Word s.val 962 clock)
    (harray : BitArray.Represents s.val.memory base width (IncidenceEncoding.words width values)) :
    ∃cost t,Executes input tape (readAdvanceCode target) cost s t ∧ cost≤2^22*(B+3)^2 ∧
      Ready (readAdvanceValues v target (values.get i)) t ∧
      (∀k∈ids,((readAdvanceValues v target (values.get i)) k).bits.length≤B) ∧
      BitArray.Represents t.val.memory base width (IncidenceEncoding.words width values) ∧
      BankArray.Word t.val 962 clock ∧ ReadFrame {target,971} s.val t.val := by
  obtain ⟨c0,a,e0,hc0,ra,aa,clocka,fa⟩ := read_executes values base width B clock hwidth hwidthB hlen
    target ht ht₀ ht₁ ht₂ hti v hv hbase hwidthv i hindex hfit input tape s hs hclock harray
  let va := Function.update v target (values.get i)
  have hva : ∀k∈ids,(va k).bits.length≤B := by
    intro k hk
    by_cases he : k=target
    · subst k;simpa only [va,Function.update_self] using hfit.trans hwidthB
    · simpa only [va,Function.update_of_ne he] using hv k hk
  obtain ⟨c1,t,e1,hc1,hb,hz,fb⟩ := NatAssign.instruction_executes ids
    (fun k hk => (by omega : 4≤960).trans (ids_ge k hk)) (.add 970 971)
    (by simp [NatAssign.Instruction.Valid,ids]) va input tape a ra.bank ra.natural
  have heval : (NatAssign.Instruction.add 970 971).update va=readAdvanceValues v target (values.get i) := by
    simp only [NatAssign.Instruction.update,NatAssign.Instruction.target,NatAssign.Instruction.value,
      va,Function.update_of_ne hti.symm,Function.update_of_ne hto.symm,hone,readAdvanceValues,Nat.add_comm]
  rw [heval] at hb
  have rt := ra.stage hb hz (fb.mono (by simp [NatAssign.changed,NatAssign.Instruction.target,ids]))
  have hind : (i.val+1).bits.length≤B := by
    apply le_trans _ hn
    simpa only [Nat.size_eq_bits_len] using Nat.size_le_size (show i.val+1≤n by omega)
  have wt : ∀k∈ids,((readAdvanceValues v target (values.get i)) k).bits.length≤B := by
    intro k hk
    by_cases he : k=971
    · subst k;simpa only [readAdvanceValues,Function.update_self,hindex] using hind
    · simpa only [readAdvanceValues,Function.update_of_ne he] using hva k hk
  have cadd : c1≤200*(2*B+4) := by
    apply hc1.trans
    exact Nat.mul_le_mul_left 200 (by have := hva 970 (by decide);have := hva 971 (by decide);omega)
  refine ⟨c0+c1,t,e0.seq e1,by nlinarith only [hc0,cadd,Nat.zero_le B],rt,wt,?_,?_,?_⟩
  · simpa only [fb.memory] using aa
  · exact BankArray.word_of_eq (fb.tapes 962 (by simp [NatAssign.changed,NatAssign.Instruction.target])) clocka
  · refine ⟨fb.memory.trans fa.memory,fb.inputHead.trans fa.inputHead,
      fb.randomCursor.trans fa.randomCursor,fb.output.trans fa.output,?_⟩
    intro k hk hnot
    have hn' : k≠target ∧ k≠971 := by
      simpa only [Finset.mem_insert,Finset.mem_singleton,not_or] using hnot
    have ht' := hn'.1
    have hi' := hn'.2
    exact (fb.tapes k (by simp only [NatAssign.changed,NatAssign.Instruction.target,Finset.mem_insert,Finset.mem_singleton];omega)).trans
      (fa.tapes k hk ht')

#print axioms readAdvance_executes
end Maxwell.Continuum.GeometryOutput
