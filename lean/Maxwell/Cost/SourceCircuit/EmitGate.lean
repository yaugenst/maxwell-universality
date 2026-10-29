import Maxwell.Cost.SourceCircuit.Common
import Maxwell.Cost.WordCall
import Maxwell.Logical.GateTrace

namespace Maxwell.Cost.SourceCircuit
open Structured
open RationalAccumulator (Blank)

def fieldsCode (archive : ℕ) : List ℕ → Code
  | [] => .skip
  | source :: rest => .seq (appendCode source archive) (fieldsCode archive rest)

def fieldCost (fields : List (ℕ × List Bool)) : ℕ :=
  (fields.map fun field => 11 * field.2.length + 10).sum + 1

theorem fields_executes (archive : ℕ) (input : List Bool) (tape : ℕ → Bool)
    (fields : List (ℕ × List Bool)) (preceding : List Bool) (s : Store)
    (hfields : ∀ field ∈ fields, field.1 ≠ archive ∧ BankArray.Word s.val field.1 field.2)
    (harchive : s.val.tapes archive = BitTape.atEnd preceding) :
    ∃ t, Executes input tape (fieldsCode archive (fields.map Prod.fst)) (fieldCost fields) s t ∧
      t.val.tapes = Function.update s.val.tapes archive
        (BitTape.atEnd (preceding ++ fields.flatMap Prod.snd)) ∧
      t.val.memory = s.val.memory ∧ Frame {archive} s.val t.val := by
  induction fields generalizing preceding s with
  | nil =>
    refine ⟨s,.skip s,?_,rfl,⟨rfl,rfl,rfl,fun _ _ _ => rfl,rfl,fun _ _ => rfl⟩⟩
    simp [← harchive]
  | cons f fields ih =>
    obtain ⟨hne,origin,hword⟩ := hfields f (by simp)
    obtain ⟨a,ea,atapes,af⟩ := append_executes f.1 archive hne input tape f.2 preceding origin s hword harchive
    have rest : ∀ field ∈ fields, field.1 ≠ archive ∧ BankArray.Word a.val field.1 field.2 := by
      intro field hf
      obtain ⟨hh,hw⟩ := hfields field (by simp [hf])
      exact ⟨hh,BankArray.word_of_eq (by simp [atapes,hh]) hw⟩
    obtain ⟨t,et,tt,tm,tf⟩ := ih (preceding ++ f.2) a rest (by simp [atapes])
    have frame : Frame {archive} s.val a.val := frame_transfer af (by
      intro j hj
      simp only [Finset.mem_singleton] at hj
      simp [atapes,hj])
    refine ⟨t,?_,?_,tm.trans af.2.2.1,frame.trans tf⟩
    · simpa [fieldsCode,fieldCost,Nat.add_assoc] using ea.seq et
    · simp [tt,atapes,List.append_assoc]

def emitGateCode (tag : List Bool) (parents : List ℕ) : Code :=
  .seq (.call (WordTransfer.clone 95 96))
    (.seq (tagCode 97 tag)
      (.seq (fieldsCode 97 parents) (BankArray.incrementCode 95)))

def gateWork : Finset ℕ := {95,96,97}

set_option maxRecDepth 8192 in
/-- Emit a gate from actual parent banks, allocate its ID, and increment
the stored next-ID word. Tags and parent tape IDs are finite code literals;
the parent identifiers and next ID remain runtime data. -/
theorem emitGate_executes (input : List Bool) (tape : ℕ → Bool)
    (tag next preceding : List Bool) (parents : List (ℕ × List Bool)) (s : Store)
    (hscratch : BankArray.Scratch s.val) (h96 : Blank s.val 96)
    (hnext : BankArray.Word s.val 95 next)
    (hparents : ∀ field ∈ parents, field.1 ≠ 96 ∧ field.1 ≠ 97 ∧ BankArray.Word s.val field.1 field.2)
    (h97 : s.val.tapes 97 = BitTape.atEnd preceding) :
    ∃ cost, ∃ t : Store,
      cost ≤ 27*next.length+6*tag.length+fieldCost parents+36 ∧
      Executes input tape (emitGateCode tag (parents.map Prod.fst)) cost s t ∧
      BankArray.Word t.val 95 (Increment.bits next) ∧ BankArray.Word t.val 96 next ∧
      t.val.tapes 97 = BitTape.atEnd (preceding ++ tag ++ parents.flatMap Prod.snd) ∧
      t.val.memory = s.val.memory ∧ BankArray.Scratch t.val ∧ Frame gateWork s.val t.val := by
  obtain ⟨origin,hnext⟩ := hnext
  obtain ⟨outOrigin,h96⟩ := h96
  obtain ⟨c,ec,ct,cf⟩ := WordCall.clone 95 96 (by omega) input tape next origin outOrigin s hnext h96
  obtain ⟨g,eg,gt,gf⟩ := tag_executes 97 input tape tag preceding c (by simpa [ct] using h97)
  obtain ⟨p,ep,pt,pm,pf⟩ := fields_executes 97 input tape parents (preceding ++ tag) g (by
    intro field hf
    obtain ⟨h96,h97,hw⟩ := hparents field hf
    exact ⟨h97,BankArray.word_of_eq (by simp [gt,ct,h96,h97]) hw⟩) (by simp [gt])
  have ps : BankArray.Scratch p.val := scratch_of_tapes hscratch (by
    intro j hj; simp [pt,gt,ct,show j ≠ 96 by omega,show j ≠ 97 by omega])
  obtain ⟨ic,t,hic,ei,tn,ts,tm,_,tk,tf⟩ := BankArray.increment_bank 95 (by omega) input tape next p
    ⟨origin,by simp [pt,gt,ct,hnext]⟩ ps
  have cframe : Frame gateWork s.val c.val := frame_transfer cf (by
    intro j hj
    have hh : j ≠ 96 := by intro he; exact hj (by simp [gateWork,he])
    simp [ct,hh])
  have gframe : Frame gateWork c.val g.val := frame_transfer gf (by
    intro j hj
    have hh : j ≠ 97 := by intro he; exact hj (by simp [gateWork,he])
    simp [gt,hh])
  have pframe : Frame gateWork g.val p.val := pf.mono (by simp [gateWork])
  have tframe : Frame gateWork p.val t.val := (frame_except tf).mono (by simp [gateWork])
  refine ⟨_,t,?_,ec.seq (eg.seq (ep.seq ei)),tn,
    ⟨outOrigin,by rw [tk 96 (by omega)]; simp [pt,gt,ct]⟩,
    by rw [tk 97 (by omega)]; simp [pt],
    tm.trans (pm.trans (gf.2.2.1.trans cf.2.2.1)),ts,
    cframe.trans (gframe.trans (pframe.trans tframe))⟩
  omega

def zeroTag : List Bool := [false,false,false]
def halfTag : List Bool := [false,false,true]
def negativeTag : List Bool := [false,true,false]
def additionTag : List Bool := [true,false,false]

def zeroCode : Code := emitGateCode zeroTag []
def halfCode : Code := emitGateCode halfTag [94]
def negativeCode : Code := emitGateCode negativeTag [94]
def additionCode : Code := emitGateCode additionTag [94,99]

end Maxwell.Cost.SourceCircuit
