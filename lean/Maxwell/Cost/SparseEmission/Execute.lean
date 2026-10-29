import Maxwell.Cost.SparseEmission.Initialize
import Maxwell.Cost.SparseEmission.GateLoop
import Maxwell.Cost.SparseEmission.ResetCounter
import Maxwell.Cost.SparseEmission.SelectorLoop
import Maxwell.Cost.SparseEmission.Length
import Maxwell.Logical.GateTraceSquare

namespace Maxwell.Cost.SparseEmission
open Structured
open RationalAccumulator (Blank)

def code : Code := .seq Initialize.code (.seq gatesCode (.seq ResetCounter.code SelectorLoop.code))
def work : Finset ℕ := {37,97,105,110,111,112,113,114,115}

structure OutputFrame (s t : BitRAMState) : Prop where
  inputHead : t.inputHead = s.inputHead
  randomCursor : t.randomCursor = s.randomCursor
  output : t.output = s.output
  memory : t.memory = s.memory
  tapes : ∀ i, (i = 4 ∨ 10 ≤ i) → i ∉ work → t.tapes i = s.tapes i
  sign : t.registers 23 = s.registers 23
  control : ∀ i, 30 ≤ i → i ≠ 40 → i ≠ 41 → i ≠ 42 → i ≠ 43 → t.registers i = s.registers i

/-- The single fixed backend consumes the compiler's actual retained gate
and output archives and writes precisely its square-system sparse entries. -/
theorem executes {n d : ℕ} (c : Logical.RationalCode n d) (output : Fin n → Fin d)
    (input : List Bool) (randomTape : ℕ → Bool) (width : ℕ) (bytes clock : List Bool)
    (clockOrigin : ℤ) (s : Store)
    (hwidth : 0 < width) (hfit : d < 2^width) (hc : clock.length = width)
    (hbytes : SourceCircuit.traceBytes width c.trace = some bytes)
    (hs : BankArray.Scratch s.val) (h7 : Blank s.val 7) (h37 : Blank s.val 37)
    (hn : BankArray.Word s.val 19 n.bits)
    (hclock : s.val.tapes 93 = BitTape.shifted clock clockOrigin)
    (h97 : s.val.tapes 97 = BitTape.atEnd bytes)
    (h105 : s.val.tapes 105 = BitTape.atEnd
      ((List.ofFn (fun i : Fin n => (output i).val)).flatMap (SourceCircuit.fixedWidth width)))
    (h110 : s.val.tapes 110 = BitTape.blank)
    (h111 : s.val.tapes 111 = BitTape.blank) (h112 : s.val.tapes 112 = BitTape.blank)
    (h113 : s.val.tapes 113 = BitTape.blank) (h114 : s.val.tapes 114 = BitTape.blank)
    (h115 : s.val.tapes 115 = BitTape.blank) :
    ∃ cost t, cost ≤ 1000*(d+1)*(width+1) ∧ Executes input randomTape code cost s t ∧
      t.val.tapes 110 = BitTape.shifted (entriesWire width (c.squareEntries output))
        (-(entriesWire width (c.squareEntries output)).length) ∧
      t.val.tapes 105 = BitTape.blank ∧ t.val.tapes 111 = BitTape.blank ∧
      t.val.tapes 112 = BitTape.blank ∧ t.val.tapes 114 = BitTape.blank ∧
      BankArray.Scratch t.val ∧ Blank t.val 7 ∧ Blank t.val 37 ∧ OutputFrame s.val t.val := by
  have hsize := c.trace_length
  have hnfit : n < 2^width := by omega
  obtain ⟨iCost,a,iBound,ea,a97,a113,a115,aScratch,a7,a37,am,af⟩ := Initialize.executes input randomTape
    width n bytes clock clockOrigin s hwidth hnfit hc hs h7 h37 hn hclock h113 h115 h97
  have ak (i : ℕ) (hi : i ∉ Initialize.work) (hi10 : 10 ≤ i) : a.val.tapes i = s.val.tapes i :=
    af.tapes i (Or.inr hi10) hi
  have aReady : Ready width n clock 0 clockOrigin a :=
    ⟨⟨a113,(ak 93 (by decide) (by omega)).trans hclock,(ak 114 (by decide) (by omega)).trans h114⟩,
      (ak 111 (by decide) (by omega)).trans h111,(ak 112 (by decide) (by omega)).trans h112⟩
  have aArchive : a.val.tapes 110 = BitTape.shifted [] 0 := by
    simpa [BitTape.shifted,BitTape.blank] using (ak 110 (by decide) (by omega)).trans h110
  obtain ⟨gCost,b,gBound,eb,b110,b97,bReady,_,bf⟩ := gates input randomTape width n c.trace bytes clock []
    0 0 clockOrigin a hbytes hc (by omega) aReady aArchive
    (a97 ▸ BitTape.shifted_represents bytes 0)
  have bCounter : b.val.tapes 113 = BitTape.shifted (SourceCircuit.fixedWidth width d) 0 := by
    simpa only [hsize] using bReady.context.rowWord
  obtain ⟨r,er,r113,_,rm,rf,rk⟩ := ResetCounter.executes input randomTape
    (SourceCircuit.fixedWidth width d) (SourceCircuit.fixedWidth width n) 0 0 b bCounter
    ((bf.tapes 115 (by decide)).trans a115)
  have rReady : SelectorLoop.Ready clock clockOrigin r :=
    ⟨(rk 93 (by decide)).trans bReady.context.clockWord,(rk 111 (by decide)).trans bReady.left,
      (rk 112 (by decide)).trans bReady.right,(rk 114 (by decide)).trans bReady.context.temporary⟩
  have r105 : r.val.tapes 105 = s.val.tapes 105 :=
    ((rk 105 (by decide)).trans (bf.tapes 105 (by decide))).trans (ak 105 (by decide) (by omega))
  obtain ⟨sCost,t,finalWord,sBound,et,t105,t110,_,_,tReady,_,_,tm,tf,tk⟩ := SelectorLoop.executes
    input randomTape width (List.ofFn (fun i : Fin n => (output i).val)) clock
    (entriesWire width (Logical.traceEntries n c.trace))
    (-(entriesWire width (Logical.traceEntries n c.trace)).length) 0 clockOrigin r hc
    (by simpa using hnfit) rReady (by simpa using r113) (r105.trans h105)
    (by simpa using (rk 110 (by decide)).trans b110)
  have finalArchive : t.val.tapes 110 = BitTape.shifted (entriesWire width (c.squareEntries output))
      (-(entriesWire width (c.squareEntries output)).length) := by
    rw [Logical.RationalCode.squareEntries_trace,entriesWire_append]
    simpa [selectorEntries_ofFn,List.length_append,Nat.cast_add,neg_add_rev,sub_eq_add_neg,add_comm] using t110
  have afterInit (i : ℕ) (hi : i < 10 ∨ i = 37) : t.val.tapes i = a.val.tapes i :=
    ((tk i (by rcases hi with hi | rfl <;> simp [SelectorLoop.work]; omega)).trans
      (rk i (by omega))).trans (bf.tapes i (by rcases hi with hi | rfl <;> simp [activeTapes]; omega))
  refine ⟨iCost+(gCost+((11*(SourceCircuit.fixedWidth width d).length+
      15*(SourceCircuit.fixedWidth width n).length+27)+sCost)),t,?_,
    ea.seq (eb.seq (er.seq et)),finalArchive,t105,tReady.left,tReady.right,tReady.temporary,
    SourceCircuit.scratch_of_tapes aScratch (fun i hi => afterInit i (Or.inl hi)),
    RationalAccumulator.blank_of_eq (afterInit 7 (Or.inl (by omega))) a7,
    RationalAccumulator.blank_of_eq (afterInit 37 (Or.inr rfl)) a37,?_⟩
  · have hbyteBound := traceBytes_length width c.trace bytes hbytes
    simp only [List.length_ofFn] at sBound
    simp only [SourceCircuit.fixedWidth_length]
    nlinarith
  · refine ⟨tf.inputHead.trans (rf.inputHead.trans (bf.inputHead.trans af.inputHead)),
      tf.randomCursor.trans (rf.randomCursor.trans (bf.randomCursor.trans af.randomCursor)),
      tf.output.trans (rf.output.trans (bf.output.trans af.output)),tm.trans (rm.trans (bf.memory.trans am)),
      ?_,tf.sign.trans (rf.sign.trans (bf.sign.trans af.sign)),?_⟩
    · intro i hi hwork
      exact ((tk i (by simp_all [work,SelectorLoop.work])).trans (rk i (by simp_all [work]))).trans
        ((bf.tapes i (by simp_all [work,activeTapes])).trans
          (af.tapes i hi (by simp_all [work,Initialize.work])))
    · intro i hi h40 h41 h42 h43
      exact (tf.control i hi).trans ((rf.control i hi).trans
        ((bf.control i hi h40 h41 h42 h43).trans (af.control i hi)))

end Maxwell.Cost.SparseEmission
