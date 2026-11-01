import Maxwell.Continuum.WellStrengthPassState
import Maxwell.Continuum.StoredGeometryCounter
import Maxwell.Continuum.NatAssignOutputWidth
import Maxwell.Cost.Structured.WordLiteral
import Maxwell.Cost.Structured.Footprint

/-! Both path passes start by executing the same packed-cursor reset,
runtime edge-count copy, and inner-counter initialization. -/
namespace Maxwell.Continuum.RationalDataflow.WellStrengthPass
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 5000000
set_option maxRecDepth 16384

def cursorPlan : List NatAssign.Instruction := [.copy 963 971,.multiply 969 971]
def cursorCode : Code := NatAssign.code cursorPlan

theorem cursor_values (v : ℕ→ℕ) : NatAssign.values cursorPlan v=Function.update v 971 (v 963*v 969) := by
  funext k
  simp [cursorPlan,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,
    NatAssign.Instruction.value,Nat.mul_comm]

theorem cursor_executes {n base width B J P first : ℕ} {data : Vector ℕ n} {clock : List Bool}
    {constants gv : ℕ→ℕ} {a : PartArray.Table J} {v : ℕ→Parts} {s : Store}
    (g : GeometryOutput.Context data base width B clock constants gv s)
    (vertices : ℕ) (hV : constants 963=vertices) (hthree : constants 969=3)
    (hspan : 3*vertices ≤ n) (hn : n.bits.length ≤ B) (state : State a P v first s)
    (input : List Bool) (tape : ℕ→Bool) :
    ∃cost t,Executes input tape cursorCode cost s t ∧ cost ≤ 2^23*(B+3)^2 ∧
      GeometryOutput.Context data base width B clock constants (Function.update gv 971 (3*vertices)) t ∧
      State a P v first t ∧ BinaryPrecision.Frame {0,1,2,3,971} s.val t.val := by
  have valid : ∀x∈cursorPlan,x.Valid GeometryOutput.ids := by
    simp [cursorPlan,NatAssign.Instruction.Valid,GeometryOutput.ids]
  obtain ⟨cost,t,e,hc,bank,scratch,frame⟩ := NatAssign.executes GeometryOutput.ids
    (fun k hk=>(by omega : 4 ≤ 960).trans (GeometryOutput.ids_ge k hk)) cursorPlan valid gv
    input tape s g.ready.bank g.ready.natural
  have changes : NatAssign.changes cursorPlan={0,1,2,3,971} := by decide
  rw [changes] at frame
  have evaluated : NatAssign.values cursorPlan gv=Function.update gv 971 (3*vertices) := by
    rw [cursor_values,g.fixed 963 (by decide),g.fixed 969 (by decide),hV,hthree,Nat.mul_comm]
  rw [evaluated] at bank
  have ready := g.ready.stage bank scratch (frame.mono (by decide))
  have indexWidth : (3*vertices).bits.length ≤ B := by
    apply le_trans _ hn
    simpa only [Nat.size_eq_bits_len] using Nat.size_le_size hspan
  have gt : GeometryOutput.Context data base width B clock constants (Function.update gv 971 (3*vertices)) t := by
    refine ⟨ready,?_,?_,BankArray.word_of_eq (frame.tapes 962 (by decide)) g.clockWord,?_⟩
    · intro k hk
      by_cases he : k=971
      · subst k;simpa only [Function.update_self] using indexWidth
      · rw [Function.update_of_ne he];exact g.wordWidth k hk
    · simpa only [frame.memory] using g.array
    · intro k hk
      rw [Function.update_of_ne (by intro he;subst k;exact (by decide : 971∉GeometryOutput.fixedIds) hk)]
      exact g.fixed k hk
  have st := state.geometry_frame ready frame.memory (frame.tapes 4 (by decide))
    (fun k hk kout _=>frame.tapes k (by simp only [Finset.mem_insert,Finset.mem_singleton];omega))
    (word_of_eq (frame.tapes 999 (by decide)) state.outputIndex)
  have cap := hc.trans (NatAssign.price_bound GeometryOutput.ids cursorPlan valid gv B g.wordWidth
    (by simp [cursorPlan,NatAssign.Instruction.literalWidth]))
  refine ⟨cost,t,e,?_,gt,st,frame⟩
  change cost ≤ 192000*(B+2)^2 at cap
  nlinarith only [cap,Nat.zero_le B]

def prepareCode : Code := .seq cursorCode (.seq (WordReplace.code 964 972) (WordLiteral.code 973 0))

theorem prepare_executes {n base width B J P first : ℕ} {data : Vector ℕ n} {clock : List Bool}
    {constants gv : ℕ→ℕ} {a : PartArray.Table J} {v : ℕ→Parts} {s : Store}
    (g : GeometryOutput.Context data base width B clock constants gv s)
    (vertices edges : ℕ) (hV : constants 963=vertices) (hE : constants 964=edges) (hthree : constants 969=3)
    (hspan : 3*vertices ≤ n) (hn : n.bits.length ≤ B) (state : State a P v first s)
    (outer inner : List Bool) (hout : BankArray.Word s.val 972 outer) (hin : BankArray.Word s.val 973 inner)
    (houter : outer.length ≤ B) (hinner : inner.length ≤ B)
    (input : List Bool) (tape : ℕ→Bool) :
    ∃cost t,Executes input tape prepareCode cost s t ∧ cost ≤ 2^23*(B+3)^2+27*B+32 ∧
      GeometryOutput.Context data base width B clock constants (Function.update gv 971 (3*vertices)) t ∧
      State a P v first t ∧ Word t.val 972 edges ∧ Blank t.val 973 ∧
      t.val.memory=s.val.memory ∧ t.val.tapes 988=s.val.tapes 988 := by
  obtain ⟨c0,u,e0,hc0,g0,state0,f0⟩ := cursor_executes g vertices hV hthree hspan hn state input tape
  obtain ⟨c1,z,e1,hc1,g1,word1,f1⟩ := GeometryOutput.loadCounter_executes g0 964 972 (by decide) (by decide)
    outer (BankArray.word_of_eq (f0.tapes 972 (by decide)) hout) houter input tape
  have state1 := state0.geometry_frame g1.ready f1.memory (e1.protectsTape 4 (by decide))
    (fun k hk kout _=>f1.tapes k hk (by simp only [Finset.mem_singleton];omega))
    (word_of_eq (f1.tapes 999 (by decide) (by decide)) state0.outputIndex)
  obtain ⟨t,e2,word2,f2⟩ := WordLiteral.executes 973 0 input tape inner z
    (BankArray.word_of_eq ((f1.tapes 973 (by decide) (by decide)).trans (f0.tapes 973 (by decide))) hin)
  have g2 := geometry_external_frame g1 (f2.mono (by decide))
  have state2 := state1.geometry_frame g2.ready f2.memory (f2.tapes 4 (by decide))
    (fun k _ kout _=>f2.tapes k (by simp only [Finset.mem_singleton];omega))
    (word_of_eq (f2.tapes 999 (by decide)) state1.outputIndex)
  have counter : Word t.val 972 edges := by
    change BankArray.Word t.val 972 edges.bits
    have w := BankArray.word_of_eq (f2.tapes 972 (by decide)) word1
    simpa only [Function.update_of_ne (by decide : (964:ℕ) ≠ 971),g.fixed 964 (by decide),hE] using w
  refine ⟨c0+(c1+(6*inner.length+11)),t,e0.seq (e1.seq e2),by omega,g2,state2,counter,
    (zero_word_iff_blank t.val 973).mp word2,f2.memory.trans (f1.memory.trans f0.memory),?_⟩
  exact (f2.tapes 988 (by decide)).trans ((f1.tapes 988 (by decide) (by decide)).trans (f0.tapes 988 (by decide)))


theorem clearOuter_executes {n base width B J P first : ℕ} {data : Vector ℕ n} {clock : List Bool}
    {constants gv : ℕ→ℕ} {a : PartArray.Table J} {v : ℕ→Parts} {s : Store}
    (g : GeometryOutput.Context data base width B clock constants gv s) (state : State a P v first s)
    (word : List Bool) (origin : ℤ) (hw : s.val.tapes 972=BitTape.shifted word origin)
    (input : List Bool) (tape : ℕ→Bool) :
    ∃t,Executes input tape (.call (TapeOps.clear 972)) (6*word.length+4) s t ∧
      GeometryOutput.Context data base width B clock constants gv t ∧ State a P v first t ∧
      Blank t.val 972 ∧ BinaryPrecision.Frame {972} s.val t.val := by
  obtain ⟨t,e,blank,frame⟩ := RuntimeCounter.clear_executes 972 input tape word origin s hw
  have gt := geometry_external_frame g (frame.mono (by decide))
  have st := state.geometry_frame gt.ready frame.memory (frame.tapes 4 (by decide))
    (fun k _ kout _=>frame.tapes k (by simp only [Finset.mem_singleton];omega))
    (word_of_eq (frame.tapes 999 (by decide)) state.outputIndex)
  exact ⟨t,e,gt,st,blank,frame⟩

#print axioms prepare_executes
end Maxwell.Continuum.RationalDataflow.WellStrengthPass
