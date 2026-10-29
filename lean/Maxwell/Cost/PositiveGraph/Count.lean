import Maxwell.Cost.PositiveGraph.CountStep
import Mathlib.Data.Nat.Size

namespace Maxwell.Cost.PositiveGraph.Count
open Structured

def peekCode : Code := Code.atom (.readTape 110 44 46)
def peekState (s : Store) : Store := Store.ofState
  {s.val with
    pc := 1
    registers := Function.update (Function.update s.val.registers 44
      ((s.val.tapes 110).read.getD false)) 46 ((s.val.tapes 110).read.isSome)}

theorem peek_executes (input : List Bool) (randomTape : ℕ → Bool) (s : Store) :
    Executes input randomTape peekCode 3 s (peekState s) := by
  apply Executes.atom (extra := 1)
  · simp [BitRAM.next,s.property,BitRAMState.setRegister]
  · rfl

theorem peek_frame (s : Store) : Frame s.val (peekState s).val := by
  constructor <;> intros <;> simp_all [peekState,Store.ofState]

@[simp] theorem peek_tapes (s : Store) : (peekState s).val.tapes = s.val.tapes := rfl

theorem peek_present (s : Store) (bytes : List Bool)
    (hs : TapeRepresents (s.val.tapes 110) bytes) :
    (peekState s).val.registers 46 = !bytes.isEmpty := by
  have h := hs 0
  cases bytes <;> simp_all [peekState,Store.ofState,BitTape.read]

def loopCode : Code := .loop 46 (.seq stepCode peekCode)
def scanCode : Code := .seq peekCode loopCode
def code : Code := .seq scanCode (.call (Rewind.program 110))

theorem wire_nonempty (width : ℕ) (e : Logical.RationalCode.Entry)
    (entries : List Logical.RationalCode.Entry) :
    (SparseEmission.entriesWire width (e::entries)).isEmpty = false := by
  have hn : (SparseEmission.entriesWire width (e::entries)).length ≠ 0 := by simp
  cases h : SparseEmission.entriesWire width (e::entries) <;> simp_all

theorem loop (input : List Bool) (randomTape : ℕ → Bool)
    (width start bound : ℕ) (entries : List Logical.RationalCode.Entry)
    (clock : List Bool) (clockOrigin countOrigin : ℤ) (s : Store)
    (hc : clock.length = width) (hbound : start+entries.length < 2^bound)
    (hr : Ready start clock clockOrigin countOrigin s)
    (hs : TapeRepresents (s.val.tapes 110) (SparseEmission.entriesWire width entries))
    (htest : s.val.registers 46 = !(SparseEmission.entriesWire width entries).isEmpty) :
    ∃ cost t, cost ≤ entries.length*(58*width+12*bound+81)+1 ∧
      Executes input randomTape loopCode cost s t ∧
      t.val.tapes 110 = SparseEmission.ReadGate.advance (s.val.tapes 110)
        (SparseEmission.entriesWire width entries).length ∧
      Ready (start+entries.length) clock clockOrigin countOrigin t ∧
      t.val.registers 46 = false ∧ Frame s.val t.val := by
  induction entries generalizing start s with
  | nil =>
    have hfalse : s.val.registers 46 = false := by simpa [SparseEmission.entriesWire] using htest
    exact ⟨1,s,by simp,Executes.done hfalse,by simp [SparseEmission.entriesWire,SparseEmission.ReadGate.advance],
      by simpa using hr,hfalse,Frame.refl _⟩
  | cons e rest ih =>
    have htrue : s.val.registers 46 = true := by rw [wire_nonempty] at htest; exact htest
    obtain ⟨sc,a,scBound,ea,a110,asuffix,ar,af⟩ := step input randomTape width start e
      (SparseEmission.entriesWire width rest) clock clockOrigin countOrigin s hc hr
      (by simpa only [SparseEmission.entriesWire,List.flatMap_cons] using hs)
    let b := peekState a
    have br : Ready (start+1) clock clockOrigin countOrigin b := ⟨ar.clock,ar.counter,ar.left,ar.right⟩
    obtain ⟨rc,t,rcBound,et,t110,tr,tfalse,tf⟩ := ih (start+1) b
      (by simp only [List.length_cons] at hbound; omega) br asuffix
      (peek_present a _ asuffix)
    have hbits : start.bits.length ≤ bound := by
      rw [Nat.size_eq_bits_len]
      exact Nat.size_le.mpr (by simp only [List.length_cons] at hbound; omega)
    refine ⟨1+(sc+3)+rc,t,?_,Executes.more htrue (ea.seq (peek_executes input randomTape a)) et,
      ?_,?_,tfalse,af.trans ((peek_frame a).trans tf)⟩
    · simp only [List.length_cons]
      nlinarith
    · rw [t110,show b.val.tapes 110 = a.val.tapes 110 from rfl,a110,SparseEmission.ReadGate.advance_add]
      simp [SparseEmission.entriesWire,List.length_flatMap]
    · convert tr using 1
      simp only [List.length_cons]
      omega

theorem executes (input : List Bool) (randomTape : ℕ → Bool)
    (width bound : ℕ) (entries : List Logical.RationalCode.Entry) (clock : List Bool)
    (origin clockOrigin countOrigin : ℤ) (s : Store)
    (hc : clock.length = width) (hbound : entries.length < 2^bound)
    (hr : Ready 0 clock clockOrigin countOrigin s)
    (hs : s.val.tapes 110 = BitTape.shifted (SparseEmission.entriesWire width entries) origin) :
    ∃ cost t, cost ≤ entries.length*(66*width+12*bound+89)+10 ∧
      Executes input randomTape code cost s t ∧
      t.val.tapes 110 = s.val.tapes 110 ∧
      Ready entries.length clock clockOrigin countOrigin t ∧ Frame s.val t.val := by
  have hrep : TapeRepresents (s.val.tapes 110) (SparseEmission.entriesWire width entries) := by
    rw [hs]
    intro j
    simp [BitTape.shifted]
  have pready : Ready 0 clock clockOrigin countOrigin (peekState s) := ⟨hr.clock,hr.counter,hr.left,hr.right⟩
  obtain ⟨lc,a,lcBound,ea,a110,ar,_atest,af⟩ := loop input randomTape width 0 bound entries clock
    clockOrigin countOrigin (peekState s) hc (by simpa using hbound) pready hrep
    (peek_present s _ hrep)
  have aend : a.val.tapes 110 = BitTape.shiftedEnd (SparseEmission.entriesWire width entries) origin := by
    simpa [SparseEmission.ReadGate.advance,hs,BitTape.shiftedEnd,BitTape.shifted] using a110
  obtain ⟨rt,t110⟩ := WordTransfer.rewind_shifted 110 origin input randomTape
    (SparseEmission.entriesWire width entries) a.val a.property aend
  let t := Store.ofState (Rewind.finishAt 110 origin a.val)
  have et : Executes input randomTape (.call (Rewind.program 110))
      (4*(SparseEmission.entriesWire width entries).length+6) a t := .call _ _ _ _ rt rfl
  have tf := WordTransfer.frame_rewind 110 110 110 (Or.inl rfl) origin a.val
  refine ⟨_,t,?_,((peek_executes input randomTape s).seq ea).seq et,?_,?_,
    (peek_frame s).trans (af.trans (Frame.of_transfer tf ?_))⟩
  · rw [SparseEmission.entriesWire_length]
    nlinarith
  · exact t110.trans hs.symm
  · constructor
    · simpa [t,Store.ofState,Rewind.finishAt] using ar.clock
    · simpa [t,Store.ofState,Rewind.finishAt] using ar.counter
    · simpa [t,Store.ofState,Rewind.finishAt] using ar.left
    · simpa [t,Store.ofState,Rewind.finishAt] using ar.right
  · intro i hi
    simp only [t,Store.ofState,Rewind.finishAt]
    exact Function.update_of_ne (by simp_all [changed]) _ _

end Maxwell.Cost.PositiveGraph.Count
