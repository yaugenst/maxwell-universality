import Maxwell.Cost.PhysicalSource.SeedArithmetic
import Maxwell.Cost.PhysicalSource.Address
import Maxwell.Cost.PhysicalSource.WriteAll

/-! A complete finite seed-record operation: compute the exact signed
rational, compute its edge address, and write all three dense arrays. -/
namespace Maxwell.Cost.PhysicalSource.SeedRecord
open Structured RationalAccumulator Overlay
set_option maxHeartbeats 1500000

def values (v : ℕ→ℕ) : Fin 3→ℕ :=
  ![SeedArithmetic.positive v,SeedArithmetic.negative v,SeedArithmetic.denominator v]

def code : Code := .seq SeedArithmetic.code (.seq Address.code writeAllCode)

def changes : Finset ℕ := {37,333,334,335,336,368,369}

structure Frame (s t : BitRAMState) : Prop where
  inputHead : t.inputHead=s.inputHead
  randomCursor : t.randomCursor=s.randomCursor
  output : t.output=s.output
  tapes : ∀ j, j=4 ∨ 10≤j → j∉changes → t.tapes j=s.tapes j

private theorem ready_after {changed : Finset ℕ} {s t : BitRAMState}
    (h : BinaryPrecision.Frame changed s t) (hs : Ready s) (ht : NatAssign.Scratch t)
    (hc : ∀ j,4≤j → j<10 → j∉changed) : Ready t := by
  intro j hj
  by_cases hh : j<4
  · exact ht j hh
  · exact blank_of_eq (h.tapes j (hc j (by omega) hj)) (hs j hj)

private theorem stored_after {n : ℕ} (l : Layout n) (words : Fin 3→Vector (List Bool) n)
    {changed : Finset ℕ} {s t : BitRAMState} (h : BinaryPrecision.Frame changed s t)
    (hs : Stored l words s) (h300 : 300∉changed) (h301 : 301∉changed)
    (hb : ∀ i,baseTape i∉changed) : Stored l words t :=
  ⟨BankArray.word_of_eq (h.tapes 300 h300) hs.width,
    BankArray.word_of_eq (h.tapes 301 h301) hs.clock,
    fun i => BankArray.word_of_eq (h.tapes (baseTape i) (hb i)) (hs.bases i),
    fun i => by simpa only [h.memory] using hs.arrays i⟩

/-- The input bank consists of parsed RHS, retained normalization/qhat,
prototype weight, and actual translated coordinates. The seed value and
address are computed here; neither is supplied as an output oracle. -/
theorem executes {n : ℕ} (l : Layout n) (words : Fin 3→Vector (List Bool) n)
    (v : ℕ→ℕ) (i : Fin n) (B : ℕ) (hB : 3≤B) (hl : l.Sized B)
    (hseed : ∀ j∈SeedArithmetic.ids,(v j).bits.length≤B)
    (haddress : ∀ j∈Address.ids,(v j).bits.length≤B)
    (hi : Address.result v=i.val) (hil : i.val.bits.length≤B)
    (hfit : ∀ port,(values v port).bits.length≤addressValue l.width)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : Ready s.val) (h37 : Blank s.val 37) (hd : Stored l words s.val)
    (hbseed : NatAssign.Bank SeedArithmetic.ids v s.val)
    (hbaddress : NatAssign.Bank Address.ids v s.val) :
    ∃ cost t, cost≤(3000*8^19+3000*8^6+120000)*(B+2)^2 ∧
      Executes input tape code cost s t ∧ Ready t.val ∧ Blank t.val 37 ∧
      Stored l (written l words i (values v)) t.val ∧
      value (written l words i (values v))=Function.update (value words) i (SeedArithmetic.value v) ∧
      Frame s.val t.val ∧ Outside l s.val t.val := by
  obtain ⟨ca,a,hca,ea,ap,an,ad,ar,af⟩ := SeedArithmetic.executes v B hB input tape s
    hbseed (fun j hj => hs j (by omega)) hseed
  have har : Ready a.val := ready_after af hs ar (by
    intro j hj hl
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or]
    omega)
  have hab : NatAssign.Bank Address.ids v a.val := by
    intro j hj
    exact word_of_eq (af.tapes j (by
      simp only [Address.ids,Finset.mem_insert,Finset.mem_singleton] at hj
      simp only [Finset.mem_insert,Finset.mem_singleton,not_or]
      omega)) (hbaddress j hj)
  have had := stored_after l words af hd (by decide) (by decide) (by
    intro j
    have := j.isLt
    simp only [baseTape,Finset.mem_insert,Finset.mem_singleton,not_or]
    omega)
  obtain ⟨cb,b,hcb,eb,bindex,br,bf⟩ := Address.executes v B input tape a hab ar haddress
  have hbr : Ready b.val := ready_after bf har br (by
    intro j hj hl
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or]
    omega)
  have hbd := stored_after l words bf had (by decide) (by decide) (by
    intro j
    have := j.isLt
    simp only [baseTape,Finset.mem_insert,Finset.mem_singleton,not_or]
    omega)
  have hv : ∀ port,Word b.val (valueTape port) (values v port) := by
    intro port
    fin_cases port
    · exact word_of_eq (bf.tapes 334 (by decide)) ap
    · exact word_of_eq (bf.tapes 335 (by decide)) an
    · exact word_of_eq (bf.tapes 336 (by decide)) ad
  obtain ⟨cc,t,hcc,ec,tr,t37,td,tm,tf⟩ := write_all l words i (values v) B hl hfit input tape
    i.val.bits (addressValue_bits _) hil b hbr
    (blank_of_eq ((bf.tapes 37 (by decide)).trans (af.tapes 37 (by decide))) h37) hbd
    (by change Word b.val 333 i.val; simpa only [hi] using bindex) hv
  refine ⟨ca+(cb+cc),t,by nlinarith,ea.seq (eb.seq ec),tr,t37,td,?_,?_,
    ((Outside.of_memory l af.memory).trans (Outside.of_memory l bf.memory)).trans
      (Outside.of_write_all l i (values v) tm)⟩
  · rw [written_value_function l words i (values v) hfit]
    exact congrArg (Function.update (value words) i) (SeedArithmetic.fraction_value v)
  · refine ⟨tf.1.trans (bf.inputHead.trans af.inputHead),
      tf.2.1.trans (bf.randomCursor.trans af.randomCursor),
      tf.2.2.1.trans (bf.output.trans af.output),?_⟩
    intro j hj hc
    simp only [changes,Finset.mem_insert,Finset.mem_singleton,not_or] at hc
    refine (tf.2.2.2.1 j hj hc.1).trans ((bf.tapes j ?_).trans (af.tapes j ?_)) <;>
      simp only [Finset.mem_insert,Finset.mem_singleton,not_or] <;> omega

end Maxwell.Cost.PhysicalSource.SeedRecord
