import Maxwell.Cost.SparseEmission.GateStep
import Maxwell.Cost.SparseEmission.Peek

namespace Maxwell.Cost.SparseEmission
open Structured

def gateLoopCode : Code := .loop 43 (.seq gateStepCode peekCode)
def gatesCode : Code := .seq peekCode gateLoopCode

theorem gate_bytes_nonempty (width : ℕ) (gate : Logical.GateRecord) (bytes : List Bool)
    (hbytes : SourceCircuit.gateBytes width gate = some bytes) : bytes.isEmpty = false := by
  obtain ⟨kind,rfl⟩ := ReadGate.exists_kind width gate bytes hbytes
  rw [← ReadGate.kind_wire_eq width kind bytes hbytes]
  simp [ReadGate.wire]

theorem gateLoop (input : List Bool) (randomTape : ℕ → Bool)
    (width start : ℕ) (gates : List Logical.GateRecord) (bytes clock preceding : List Bool)
    (origin rowOrigin clockOrigin : ℤ) (s : Store)
    (hbytes : SourceCircuit.traceBytes width gates = some bytes)
    (hc : clock.length = width) (hroom : start+gates.length < 2^width)
    (hready : Ready width start clock rowOrigin clockOrigin s)
    (ha : s.val.tapes 110 = BitTape.shifted preceding origin)
    (hs : TapeRepresents (s.val.tapes 97) bytes)
    (htest : s.val.registers 43 = !bytes.isEmpty) :
    ∃ cost t, cost ≤ gates.length*(210*width+239)+1 ∧ Executes input randomTape gateLoopCode cost s t ∧
      t.val.tapes 110 = BitTape.shifted (entriesWire width (Logical.traceEntries start gates)++preceding)
        (origin-(entriesWire width (Logical.traceEntries start gates)).length) ∧
      t.val.tapes 97 = ReadGate.advance (s.val.tapes 97) bytes.length ∧
      Ready width (start+gates.length) clock rowOrigin clockOrigin t ∧
      t.val.registers 43 = false ∧ Frame s.val t.val := by
  induction gates generalizing start bytes preceding origin s with
  | nil =>
    have hnil : bytes = [] := by simpa [SourceCircuit.traceBytes] using hbytes.symm
    subst bytes
    have ht : s.val.registers 43 = false := by simpa using htest
    refine ⟨1,s,by simp,Executes.done ht,?_,?_,?_,ht,Frame.refl _⟩
    · simpa [Logical.traceEntries,entriesWire] using ha
    · simp [ReadGate.advance]
    · simpa using hready
  | cons gate rest ih =>
    cases hhead : SourceCircuit.gateBytes width gate with
    | none => simp [SourceCircuit.traceBytes,hhead] at hbytes
    | some head =>
      cases htail : SourceCircuit.traceBytes width rest with
      | none => simp [SourceCircuit.traceBytes,hhead,htail] at hbytes
      | some tail =>
        have hb : head++tail = bytes := by simpa [SourceCircuit.traceBytes,hhead,htail] using hbytes
        subst bytes
        have htrue : s.val.registers 43 = true := by
          have hn := gate_bytes_nonempty width gate head hhead
          cases head <;> simp_all
        obtain ⟨aCost,a,aBound,ea,a110,a97,aSuffix,aReady,af⟩ := gateStep input randomTape width start
          gate head tail clock preceding origin rowOrigin clockOrigin s hhead hc
          (by simp only [List.length_cons] at hroom; omega) hready ha hs
        let b := peekState a
        have eb : Executes input randomTape peekCode 3 a b := peek_executes input randomTape a
        have bReady : Ready width (start+1) clock rowOrigin clockOrigin b :=
          ⟨⟨aReady.context.rowWord,aReady.context.clockWord,aReady.context.temporary⟩,
            aReady.left,aReady.right⟩
        have bTest : b.val.registers 43 = !tail.isEmpty := peek_present a tail aSuffix
        obtain ⟨rCost,t,rBound,et,t110,t97,tReady,tFalse,tf⟩ := ih (start+1) tail
          (entriesWire width (gate.entries start)++preceding)
          (origin-(entriesWire width (gate.entries start)).length) b htail
          (by simp only [List.length_cons] at hroom; omega) bReady a110 aSuffix bTest
        have source : t.val.tapes 97 = ReadGate.advance (s.val.tapes 97) (head++tail).length := by
          rw [t97,show b.val.tapes 97 = a.val.tapes 97 from rfl,a97,ReadGate.advance_add,List.length_append]
        refine ⟨1+(aCost+3)+rCost,t,?_,Executes.more htrue (ea.seq eb) et,?_,source,?_,tFalse,
          af.trans ((peek_frame a).trans tf)⟩
        · simp only [List.length_cons]
          nlinarith
        · simpa [Logical.traceEntries,entriesWire_append,List.append_assoc,List.length_append,
            Nat.cast_add,sub_sub,add_comm] using t110
        · convert tReady using 1; simp only [List.length_cons]; omega

theorem gates (input : List Bool) (randomTape : ℕ → Bool)
    (width start : ℕ) (gates : List Logical.GateRecord) (bytes clock preceding : List Bool)
    (origin rowOrigin clockOrigin : ℤ) (s : Store)
    (hbytes : SourceCircuit.traceBytes width gates = some bytes)
    (hc : clock.length = width) (hroom : start+gates.length < 2^width)
    (hready : Ready width start clock rowOrigin clockOrigin s)
    (ha : s.val.tapes 110 = BitTape.shifted preceding origin)
    (hs : TapeRepresents (s.val.tapes 97) bytes) :
    ∃ cost t, cost ≤ gates.length*(210*width+239)+4 ∧ Executes input randomTape gatesCode cost s t ∧
      t.val.tapes 110 = BitTape.shifted (entriesWire width (Logical.traceEntries start gates)++preceding)
        (origin-(entriesWire width (Logical.traceEntries start gates)).length) ∧
      t.val.tapes 97 = ReadGate.advance (s.val.tapes 97) bytes.length ∧
      Ready width (start+gates.length) clock rowOrigin clockOrigin t ∧
      t.val.registers 43 = false ∧ Frame s.val t.val := by
  obtain ⟨cost,t,hcost,et,ta,ts,tr,tf,frame⟩ := gateLoop input randomTape width start gates bytes clock
    preceding origin rowOrigin clockOrigin (peekState s) hbytes hc hroom
    ⟨⟨hready.context.rowWord,hready.context.clockWord,hready.context.temporary⟩,hready.left,hready.right⟩ ha hs
    (peek_present s bytes hs)
  exact ⟨3+cost,t,by omega,(peek_executes input randomTape s).seq et,ta,ts,tr,tf,
    (peek_frame s).trans frame⟩

end Maxwell.Cost.SparseEmission
