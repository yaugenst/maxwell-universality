import Maxwell.Cost.SparseEmission.GateDispatch
import Maxwell.Cost.SparseEmission.Common

namespace Maxwell.Cost.SparseEmission
open Structured

structure Ready (width id : ℕ) (clock : List Bool) (rowOrigin clockOrigin : ℤ) (s : Store) : Prop where
  context : GateEmit.Context (SourceCircuit.fixedWidth width id) clock rowOrigin clockOrigin s
  left : s.val.tapes 111 = BitTape.blank
  right : s.val.tapes 112 = BitTape.blank

def gateStepCode : Code := .seq ReadGate.code (.seq GateDispatch.code incrementCode)

theorem gateStep (input : List Bool) (randomTape : ℕ → Bool)
    (width id : ℕ) (gate : Logical.GateRecord) (bytes suffix clock preceding : List Bool)
    (origin rowOrigin clockOrigin : ℤ) (s : Store)
    (hbytes : SourceCircuit.gateBytes width gate = some bytes)
    (hc : clock.length = width) (hroom : id+1 < 2^width)
    (hready : Ready width id clock rowOrigin clockOrigin s)
    (ha : s.val.tapes 110 = BitTape.shifted preceding origin)
    (hs : TapeRepresents (s.val.tapes 97) (bytes++suffix)) :
    ∃ cost t, cost ≤ 210*width+235 ∧ Executes input randomTape gateStepCode cost s t ∧
      t.val.tapes 110 = BitTape.shifted (entriesWire width (gate.entries id)++preceding)
        (origin-(entriesWire width (gate.entries id)).length) ∧
      t.val.tapes 97 = ReadGate.advance (s.val.tapes 97) bytes.length ∧
      TapeRepresents (t.val.tapes 97) suffix ∧
      Ready width (id+1) clock rowOrigin clockOrigin t ∧ Frame s.val t.val := by
  obtain ⟨kind,rfl⟩ := ReadGate.exists_kind width gate bytes hbytes
  have hb := ReadGate.kind_wire_eq width kind bytes hbytes
  obtain ⟨aCost,a,aBound,ea,a97,aSuffix,a111,a112,aTags,af⟩ := ReadGate.executes input randomTape
    kind.a kind.b kind.c (kind.leftWord width) (kind.rightWord width) suffix clock width clockOrigin
    (by simp) (by simp) hc s (by simpa only [hb] using hs)
    hready.context.clockWord hready.left hready.right
  have aContext : GateEmit.Context (SourceCircuit.fixedWidth width id) clock rowOrigin clockOrigin a :=
    ⟨(af.tapes 113 (by decide) (by decide) (by decide)).trans hready.context.rowWord,
      (af.tapes 93 (by decide) (by decide) (by decide)).trans hready.context.clockWord,
      (af.tapes 114 (by decide) (by decide) (by decide)).trans hready.context.temporary⟩
  obtain ⟨bCost,b,bBound,eb,b110,b111,b112,bContext,ba,bm,bf,bk⟩ := GateDispatch.executes kind
    input randomTape (SourceCircuit.fixedWidth width id) clock preceding origin rowOrigin clockOrigin a
    (by simpa using hc) aContext ((af.tapes 110 (by decide) (by decide) (by decide)).trans ha)
    (by simpa using a111) (by simpa using a112) aTags
  obtain ⟨iCost,t,iBound,et,t113,tf,tk⟩ := increment_executes input randomTape width id rowOrigin b hroom bContext.rowWord
  have archive : t.val.tapes 110 = BitTape.shifted
      (entriesWire width (kind.record.entries id)++preceding)
      (origin-(entriesWire width (kind.record.entries id)).length) := by
    rw [tk 110 (by decide),b110,SourceCircuit.fixedWidth_length,GateDispatch.group_entries]
  have source : t.val.tapes 97 = ReadGate.advance (s.val.tapes 97) bytes.length := by
    rw [tk 97 (by decide),bk 97 (by decide),a97,hb]
  have ready : Ready width (id+1) clock rowOrigin clockOrigin t :=
    ⟨⟨t113,(tk 93 (by decide)).trans bContext.clockWord,
      (tk 114 (by decide)).trans bContext.temporary⟩,
      (tk 111 (by decide)).trans b111,(tk 112 (by decide)).trans b112⟩
  refine ⟨aCost+(bCost+iCost),t,?_,ea.seq (eb.seq et),archive,source,?_,ready,?_⟩
  · simp only [SourceCircuit.fixedWidth_length] at bBound
    omega
  · rw [tk 97 (by decide),bk 97 (by decide)]
    exact aSuffix
  · exact ((Frame.of_reader af).trans (Frame.of_emitter (by decide) bf ba bm bk)).trans tf

end Maxwell.Cost.SparseEmission
