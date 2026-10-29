import Maxwell.Cost.PositiveGraph.Parse
import Maxwell.Cost.SparseEmission.Encoding
import Maxwell.Cost.WordReset
import Maxwell.Cost.WordLength
import Maxwell.Cost.Structured.Primitive

namespace Maxwell.Cost.PositiveGraph.Count
open Structured

def changed : Finset ℕ := {110,111,112,116}

structure Frame (s t : BitRAMState) : Prop where
  address : t.address = s.address
  memory : t.memory = s.memory
  inputHead : t.inputHead = s.inputHead
  randomCursor : t.randomCursor = s.randomCursor
  output : t.output = s.output
  tapes : ∀ i, i ∉ changed → t.tapes i = s.tapes i
  sign : t.registers 23 = s.registers 23
  control : ∀ i, 30 ≤ i → i ≠ 44 → i ≠ 45 → i ≠ 46 → t.registers i = s.registers i

theorem Frame.refl (s : BitRAMState) : Frame s s := by constructor <;> intros <;> rfl
theorem Frame.trans {s t u : BitRAMState} (h : Frame s t) (k : Frame t u) : Frame s u :=
  ⟨k.address.trans h.address,k.memory.trans h.memory,k.inputHead.trans h.inputHead,
    k.randomCursor.trans h.randomCursor,k.output.trans h.output,
    fun i hi => (k.tapes i hi).trans (h.tapes i hi),k.sign.trans h.sign,
    fun i a b c d => (k.control i a b c d).trans (h.control i a b c d)⟩

theorem Frame.of_parse {s t : BitRAMState} (h : Parse.Frame s t) : Frame s t :=
  ⟨h.address,h.memory,h.inputHead,h.randomCursor,h.output,
    fun i hi => h.tapes i (by simp_all [changed]) (by simp_all [changed])
      (by simp_all [changed]),h.sign,h.control⟩

theorem Frame.of_transfer {source target : ℕ} {s t : BitRAMState}
    (h : WordTransfer.Frame source target s t)
    (ht : ∀ i ∉ changed, t.tapes i = s.tapes i) : Frame s t :=
  ⟨h.1,h.2.2.1,h.2.1,h.2.2.2.1,h.2.2.2.2.1,ht,
    h.2.2.2.2.2.2 23 (by omega) (by omega) (by omega) (by omega),
    fun i hi _ _ _ => h.2.2.2.2.2.2 i (by omega) (by omega) (by omega) (by omega)⟩

def incrementCode : Code := BankArray.incrementCode 116

theorem increment (input : List Bool) (randomTape : ℕ → Bool) (n : ℕ) (origin : ℤ) (s : Store)
    (hw : s.val.tapes 116 = BitTape.shifted n.bits origin) :
    ∃ cost t, cost ≤ 12*n.bits.length+18 ∧ Executes input randomTape incrementCode cost s t ∧
      t.val.tapes 116 = BitTape.shifted (n+1).bits origin ∧ Frame s.val t.val ∧
      (∀ i, i ≠ 116 → t.val.tapes i = s.val.tapes i) := by
  have hbits : Increment.bits n.bits = (n+1).bits := by
    rw [← WordLength.countBits_eq n,← WordLength.countBits_eq (n+1)]
    rfl
  obtain ⟨cost,u,hcost,eu,up,uw,uf⟩ := Increment.simulation 116 input randomTape n.bits origin s.val s.property hw
  let a := Store.ofState u
  have ea : Executes input randomTape (.call (Increment.program 116)) (cost+1) s a :=
    .call _ _ _ _ eu (by rw [up]; rfl)
  have hr := WordTransfer.rewind_shifted 116 origin input randomTape (Increment.bits n.bits) a.val a.property uw
  let t := Store.ofState (Rewind.finishAt 116 origin a.val)
  have et : Executes input randomTape (.call (Rewind.program 116)) (4*(Increment.bits n.bits).length+6) a t :=
    .call _ _ _ _ hr.1 rfl
  have rf : WordTransfer.Frame 116 116 a.val t.val := WordTransfer.frame_rewind 116 116 116 (Or.inl rfl) origin a.val
  have keep (i : ℕ) (hi : i ≠ 116) : t.val.tapes i = s.val.tapes i :=
    (rf.2.2.2.2.2.1 i hi hi).trans (uf.2.2.2.2.2.1 i hi)
  refine ⟨_,t,?_,ea.seq et,?_,?_,keep⟩
  · have := Increment.bits_length_le n.bits
    omega
  · simpa only [t,Store.ofState,hbits] using hr.2
  · refine ⟨rf.1.trans uf.1,rf.2.2.1.trans uf.2.2.1,rf.2.1.trans uf.2.1,
      rf.2.2.2.1.trans uf.2.2.2.1,rf.2.2.2.2.1.trans uf.2.2.2.2.1,
      fun i hi => keep i (by simp_all [changed]),?_,?_⟩
    · exact (rf.2.2.2.2.2.2 23 (by omega) (by omega) (by omega) (by omega)).trans
        (uf.2.2.2.2.2.2 23 (by omega) (by omega) (by omega) (by omega))
    · intro i hi _ _ _
      exact (rf.2.2.2.2.2.2 i (by omega) (by omega) (by omega) (by omega)).trans
        (uf.2.2.2.2.2.2 i (by omega) (by omega) (by omega) (by omega))

structure Ready (count : ℕ) (clock : List Bool) (clockOrigin countOrigin : ℤ) (s : Store) : Prop where
  clock : s.val.tapes 93 = BitTape.shifted clock clockOrigin
  counter : s.val.tapes 116 = BitTape.shifted count.bits countOrigin
  left : s.val.tapes 111 = BitTape.blank
  right : s.val.tapes 112 = BitTape.blank

def stepCode : Code := .seq Parse.code
  (.seq (WordCall.resetStart 111) (.seq (WordCall.resetStart 112) incrementCode))

theorem step (input : List Bool) (randomTape : ℕ → Bool) (width count : ℕ)
    (entry : Logical.RationalCode.Entry) (suffix clock : List Bool) (clockOrigin countOrigin : ℤ) (s : Store)
    (hc : clock.length = width) (hr : Ready count clock clockOrigin countOrigin s)
    (hs : TapeRepresents (s.val.tapes 110) (SparseEmission.entryWire width entry++suffix)) :
    ∃ cost t, cost ≤ 58*width+12*count.bits.length+77 ∧ Executes input randomTape stepCode cost s t ∧
      t.val.tapes 110 = SparseEmission.ReadGate.advance (s.val.tapes 110) (2*width+2) ∧
      TapeRepresents (t.val.tapes 110) suffix ∧ Ready (count+1) clock clockOrigin countOrigin t ∧
      Frame s.val t.val := by
  let row := SourceCircuit.fixedWidth width entry.row
  let column := SourceCircuit.fixedWidth width entry.column
  have hrow : row.length = width := SourceCircuit.fixedWidth_length _ _
  have hcol : column.length = width := SourceCircuit.fixedWidth_length _ _
  obtain ⟨a,ea,a110,asuffix,a111,a112,_aneg,_ahalf,af⟩ := Parse.executes input randomTape
    row column clock suffix (decide (entry.value<0)) (decide (entry.value=1/2 ∨ entry.value= -1/2))
    clockOrigin s (hcol.trans hrow.symm) (hc.trans hrow.symm)
    (by simpa only [SparseEmission.entryWire,SparseEmission.valueBits,List.append_assoc] using hs)
    hr.clock hr.left hr.right
  obtain ⟨b,eb,bt,bf⟩ := WordCall.reset_start 111 input randomTape row 0 a a111
  obtain ⟨c,ec,ct,cf⟩ := WordCall.reset_start 112 input randomTape column 0 b (by simpa [bt] using a112)
  have c116 : c.val.tapes 116 = BitTape.shifted count.bits countOrigin := by
    simpa [ct,bt] using (af.tapes 116 (by decide) (by decide) (by decide)).trans hr.counter
  obtain ⟨ic,t,icBound,et,t116,tf,tk⟩ := increment input randomTape count countOrigin c c116
  have bcframe : Frame a.val c.val :=
    (Frame.of_transfer bf (by intro i hi; simp_all [changed])).trans
      (Frame.of_transfer cf (by intro i hi; simp_all [changed]))
  have t110 : t.val.tapes 110 = a.val.tapes 110 := by simpa [ct,bt] using tk 110 (by decide)
  refine ⟨_,t,?_,ea.seq (eb.seq (ec.seq et)),?_,t110 ▸ asuffix,?_,(Frame.of_parse af).trans (bcframe.trans tf)⟩
  · rw [hrow,hcol]
    omega
  · rw [t110,a110,hrow]
  · refine ⟨?_,t116,?_,?_⟩
    · simpa [ct,bt] using (tk 93 (by decide)).trans
        (by simpa [ct,bt] using (af.tapes 93 (by decide) (by decide) (by decide)).trans hr.clock)
    · rw [tk 111 (by decide),ct,bt]
      rfl
    · rw [tk 112 (by decide),ct]
      rfl

end Maxwell.Cost.PositiveGraph.Count
