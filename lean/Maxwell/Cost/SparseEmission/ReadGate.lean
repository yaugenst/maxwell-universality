import Maxwell.Cost.SparseEmission.ReadField
import Maxwell.Cost.SourceCircuit.TraceBinding

/-! Read one archived gate using literal tag instructions and charged
fixed-width field copies. No parser function acts as a machine oracle. -/
namespace Maxwell.Cost.SparseEmission.ReadGate
open Structured

/-- The two parent fields are copied only on branches which consume them. -/
def fields : Code := .branch 40
  (.seq (ReadField.code 97 93 111) (ReadField.code 97 93 112))
  (.branch 41 (ReadField.code 97 93 111)
    (.branch 42 (ReadField.code 97 93 111) .skip))

def tagProgram : BitRAM := ⟨[.readTape 97 40 43,.tapeRight 97,
  .readTape 97 41 43,.tapeRight 97,.readTape 97 42 43,.tapeRight 97,.halt]⟩

def code : Code := .seq (.call tagProgram) fields

def advance (t : BitTape) (n : ℕ) : BitTape := {t with head := t.head+n}

theorem advance_add (t : BitTape) (a b : ℕ) : advance (advance t a) b = advance t (a+b) := by
  simp [advance,Nat.cast_add,add_assoc]

theorem advance_represents (t : BitTape) (word suffix : List Bool)
    (h : TapeRepresents t (word++suffix)) : TapeRepresents (advance t word.length) suffix := by
  intro k
  have hh := h (word.length+k)
  simpa [advance,Nat.cast_add,add_assoc,List.getElem?_append] using hh

structure Frame (s t : BitRAMState) : Prop where
  address : t.address = s.address
  memory : t.memory = s.memory
  inputHead : t.inputHead = s.inputHead
  randomCursor : t.randomCursor = s.randomCursor
  output : t.output = s.output
  tapes : ∀ i, i ≠ 97 → i ≠ 111 → i ≠ 112 → t.tapes i = s.tapes i
  sign : t.registers 23 = s.registers 23
  control : ∀ i, 30 ≤ i → i ≠ 40 → i ≠ 41 → i ≠ 42 → i ≠ 43 → t.registers i = s.registers i

theorem Frame.refl (s : BitRAMState) : Frame s s := by constructor <;> intros <;> rfl

theorem Frame.trans {s t u : BitRAMState} (h : Frame s t) (k : Frame t u) : Frame s u :=
  ⟨k.address.trans h.address,k.memory.trans h.memory,k.inputHead.trans h.inputHead,
    k.randomCursor.trans h.randomCursor,k.output.trans h.output,
    fun i a b c => (k.tapes i a b c).trans (h.tapes i a b c),k.sign.trans h.sign,
    fun i a b c d e => (k.control i a b c d e).trans (h.control i a b c d e)⟩

def tagState (s : BitRAMState) (a b c : Bool) : BitRAMState :=
  {s with
    pc := 6
    registers := Function.update (Function.update (Function.update (Function.update s.registers 40 a) 41 b) 42 c) 43 true
    tapes := Function.update s.tapes 97 (advance (s.tapes 97) 3)}

theorem tag_executes (input : List Bool) (randomTape : ℕ → Bool) (a b c : Bool)
    (suffix : List Bool) (s : Store) (hs : TapeRepresents (s.val.tapes 97) (a::b::c::suffix)) :
    Executes input randomTape (.call tagProgram) 10 s (Store.ofState (tagState s.val a b c)) := by
  have h0 : (s.val.tapes 97).cells (s.val.tapes 97).head = some a := by simpa using hs 0
  have h1 : (s.val.tapes 97).cells ((s.val.tapes 97).head+1) = some b := by simpa using hs 1
  have h2 : (s.val.tapes 97).cells ((s.val.tapes 97).head+2) = some c := by simpa using hs 2
  apply Executes.call tagProgram s (tagState s.val a b c) 9
  · apply executeInstructions_sound (instructions := 6)
    simp [executeInstructions,tagProgram,BitRAM.next,s.property,BitRAMState.setRegister,BitRAMState.setTape,
      BitTape.read,h0,h1,h2,tagState,advance,add_assoc]
    funext i
    by_cases hi : i = 43 <;> simp [Function.update_apply,hi]
  · rfl

theorem tag_frame (s : BitRAMState) (a b c : Bool) : Frame s (tagState s a b c) := by
  constructor <;> intros <;> simp_all [tagState]

def payload (a b c : Bool) (left right : List Bool) : List Bool :=
  if a then left++right else if b || c then left else []

def wire (a b c : Bool) (left right : List Bool) : List Bool := [a,b,c]++payload a b c left right

def Tags (s : BitRAMState) (a b c : Bool) : Prop :=
  s.registers 40 = a ∧ s.registers 41 = b ∧ s.registers 42 = c

theorem Tags.of_field {s t : BitRAMState} {target : ℕ} {a b c : Bool}
    (h : SourceCircuit.Frame {97,target} s t) (hs : Tags s a b c) : Tags t a b c :=
  ⟨(h.control 40 (by omega)).trans hs.1,
    (h.control 41 (by omega)).trans hs.2.1,(h.control 42 (by omega)).trans hs.2.2⟩

theorem Frame.of_field {s t : BitRAMState} {target : ℕ} (ht : target = 111 ∨ target = 112)
    (ha : t.address = s.address) (hm : t.memory = s.memory)
    (h : SourceCircuit.Frame {97,target} s t)
    (hk : ∀ i, i ≠ 97 → i ≠ target → t.tapes i = s.tapes i) : Frame s t :=
  ⟨ha,hm,h.inputHead,h.randomCursor,h.output,
    fun i h97 h111 h112 => hk i h97 (by rcases ht with rfl | rfl <;> assumption),h.sign,
    fun i hi _ _ _ _ => h.control i hi⟩

/-- All three tag bits govern literal branches; parent words are copied
from the archive itself and both clock and unrelated memory survive. -/
theorem fields_executes (input : List Bool) (randomTape : ℕ → Bool)
    (a b c : Bool) (left right suffix clockWord : List Bool) (width : ℕ) (clockOrigin : ℤ)
    (hl : left.length = width) (hr : right.length = width) (hc : clockWord.length = width)
    (s : Store) (hs : TapeRepresents (s.val.tapes 97) (payload a b c left right ++ suffix))
    (hclock : s.val.tapes 93 = BitTape.shifted clockWord clockOrigin)
    (h111 : s.val.tapes 111 = BitTape.blank) (h112 : s.val.tapes 112 = BitTape.blank)
    (htag : Tags s.val a b c) :
    ∃ cost t, cost ≤ 28*width+21 ∧ Executes input randomTape fields cost s t ∧
      t.val.tapes 97 = advance (s.val.tapes 97) (payload a b c left right).length ∧
      t.val.tapes 111 = (if a || b || c then BitTape.atEnd left else BitTape.blank) ∧
      t.val.tapes 112 = (if a then BitTape.atEnd right else BitTape.blank) ∧
      Tags t.val a b c ∧ Frame s.val t.val := by
  cases a with
  | true =>
    have hs' : TapeRepresents (s.val.tapes 97) (left++(right++suffix)) := by
      simpa [payload,List.append_assoc] using hs
    obtain ⟨u,eu,us,ut,ua,um,uf,uk⟩ := ReadField.executes 97 93 111
      (by omega) (by omega) (by omega) input randomTape left (right++suffix) clockWord clockOrigin s
      (hc.trans hl.symm) hclock hs' h111
    have urs : TapeRepresents (u.val.tapes 97) (right++suffix) := by
      rw [us]
      exact advance_represents _ left (right++suffix) hs'
    obtain ⟨t,et,ts,tt,ta,tm,tf,tk⟩ := ReadField.executes 97 93 112
      (by omega) (by omega) (by omega) input randomTape right suffix clockWord clockOrigin u
      (hc.trans hr.symm) ((uk 93 (by omega) (by omega)).trans hclock) urs
      ((uk 112 (by omega) (by omega)).trans h112)
    refine ⟨1+((14*left.length+10)+(14*right.length+10)),t,by omega,
      Executes.yes htag.1 (eu.seq et),?_,?_,?_,Tags.of_field tf (Tags.of_field uf htag),
      (Frame.of_field (Or.inl rfl) ua um uf uk).trans (Frame.of_field (Or.inr rfl) ta tm tf tk)⟩
    · rw [ts,us]
      simp [payload,advance,add_assoc,Nat.cast_add]
    · simpa using (tk 111 (by omega) (by omega)).trans ut
    · simpa using tt
  | false =>
    by_cases hbc : (b || c) = true
    · have hbcor : b = true ∨ c = true := by simpa only [Bool.or_eq_true] using hbc
      have hs' : TapeRepresents (s.val.tapes 97) (left++suffix) := by simpa [payload,hbcor] using hs
      obtain ⟨t,et,ts,tt,ta,tm,tf,tk⟩ := ReadField.executes 97 93 111
        (by omega) (by omega) (by omega) input randomTape left suffix clockWord clockOrigin s
        (hc.trans hl.symm) hclock hs' h111
      refine ⟨(if b then 2 else 3)+(14*left.length+10),t,?_,?_,?_,?_,?_,
        Tags.of_field tf htag,Frame.of_field (Or.inl rfl) ta tm tf tk⟩
      · cases b <;> simp <;> omega
      · cases b with
        | true =>
          have he : Executes input randomTape fields (1+(1+(14*left.length+10))) s t :=
            Executes.no htag.1 (Executes.yes htag.2.1 et)
          convert he using 1
          norm_num
          omega
        | false =>
          have hc' : c = true := by simpa using hbc
          subst c
          have he : Executes input randomTape fields (1+(1+(1+(14*left.length+10)))) s t :=
            Executes.no htag.1 (Executes.no htag.2.1 (Executes.yes htag.2.2 et))
          convert he using 1
          norm_num
          omega
      · simpa [payload,hbcor,advance] using ts
      · simpa [hbcor] using tt
      · simpa using (tk 112 (by omega) (by omega)).trans h112
    · have hb : b = false := by cases b <;> simp_all
      have hc' : c = false := by cases c <;> simp_all
      subst b c
      refine ⟨4,s,by omega,Executes.no htag.1 (Executes.no htag.2.1 (Executes.no htag.2.2 (.skip s))),
        ?_,?_,?_,htag,Frame.refl _⟩
      · simp [payload,advance]
      · simpa using h111
      · simpa using h112

/-- Complete gate reader with the literal charged bound, preserving the
unread archive suffix and every unrelated tape and memory bit. -/
theorem executes (input : List Bool) (randomTape : ℕ → Bool)
    (a b c : Bool) (left right suffix clockWord : List Bool) (width : ℕ) (clockOrigin : ℤ)
    (hl : left.length = width) (hr : right.length = width) (hc : clockWord.length = width)
    (s : Store) (hs : TapeRepresents (s.val.tapes 97) (wire a b c left right ++ suffix))
    (hclock : s.val.tapes 93 = BitTape.shifted clockWord clockOrigin)
    (h111 : s.val.tapes 111 = BitTape.blank) (h112 : s.val.tapes 112 = BitTape.blank) :
    ∃ cost t, cost ≤ 28*width+31 ∧ Executes input randomTape code cost s t ∧
      t.val.tapes 97 = advance (s.val.tapes 97) (wire a b c left right).length ∧
      TapeRepresents (t.val.tapes 97) suffix ∧
      t.val.tapes 111 = (if a || b || c then BitTape.atEnd left else BitTape.blank) ∧
      t.val.tapes 112 = (if a then BitTape.atEnd right else BitTape.blank) ∧
      Tags t.val a b c ∧ Frame s.val t.val := by
  let u := Store.ofState (tagState s.val a b c)
  have etag : Executes input randomTape (.call tagProgram) 10 s u :=
    tag_executes input randomTape a b c (payload a b c left right++suffix) s (by simpa [wire] using hs)
  have ut : u.val.tapes 97 = advance (s.val.tapes 97) 3 := by simp [u,Store.ofState,tagState]
  have uk (i : ℕ) (hi : i ≠ 97) : u.val.tapes i = s.val.tapes i := by simp [u,Store.ofState,tagState,hi]
  have uh : TapeRepresents (u.val.tapes 97) (payload a b c left right++suffix) := by
    rw [ut]
    exact advance_represents _ [a,b,c] (payload a b c left right++suffix) (by simpa [wire] using hs)
  have tags : Tags u.val a b c := by simp [Tags,u,Store.ofState,tagState]
  obtain ⟨cost,t,hcost,et,ts,tl,tr,tagsT,tf⟩ := fields_executes input randomTape a b c
    left right suffix clockWord width clockOrigin hl hr hc u uh
    ((uk 93 (by omega)).trans hclock) ((uk 111 (by omega)).trans h111)
    ((uk 112 (by omega)).trans h112) tags
  have source : t.val.tapes 97 = advance (s.val.tapes 97) (wire a b c left right).length := by
    rw [ts,ut,advance_add]
    congr 1
    simp only [wire,List.length_append,List.length_cons,List.length_nil]
  refine ⟨10+cost,t,by omega,etag.seq et,source,?_,tl,tr,tagsT,?_⟩
  · rw [source]
    exact advance_represents _ (wire a b c left right) suffix hs
  · have f := tag_frame s.val a b c
    have uf : Frame s.val u.val := ⟨f.address,f.memory,f.inputHead,f.randomCursor,f.output,f.tapes,f.sign,f.control⟩
    exact uf.trans tf

end Maxwell.Cost.SparseEmission.ReadGate
