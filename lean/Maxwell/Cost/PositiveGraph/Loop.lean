import Maxwell.Cost.PositiveGraph.Fold
import Maxwell.Cost.PositiveGraph.Count

namespace Maxwell.Cost.PositiveGraph.Loop
open Structured

def code : Code := .loop 46 (.seq Step.code Count.peekCode)
def passCode : Code := .seq Count.peekCode code

theorem peek_frame (s : Store) : Frame workBanks s.val (Count.peekState s).val := by
  constructor <;> intros <;> simp_all [Count.peekState,Store.ofState]

theorem executes (input : List Bool) (randomTape : ℕ → Bool)
    (width dimension count index base : ℕ) (entries : List (BoundedEntry dimension))
    (sourceClock endpointClock diagonalClock : List Bool) (s : Store)
    (hfit : index+entries.length ≤ count) (hcount : count ≤ 3*dimension)
    (hdimension : dimension < 2^width) (hsep : 4*count*(width+3) ≤ base)
    (hd : Descriptor width dimension base sourceClock endpointClock diagonalClock s.val)
    (hc : Cursors dimension count index s.val) (hw : Workspace s.val)
    (tables : Tables dimension count) (htables : tables.Represents width base s.val.memory)
    (hsource : TapeRepresents (s.val.tapes 110) (recordsWire width entries))
    (htest : s.val.registers 46 = !(recordsWire width entries).isEmpty) :
    ∃ cost t, cost ≤ foldPrice width dimension count index base diagonalClock entries hfit tables ∧
      Executes input randomTape code cost s t ∧
      t.val.tapes 110 = SparseEmission.ReadGate.advance (s.val.tapes 110) (recordsWire width entries).length ∧
      t.val.memory = foldMemory width dimension count index base entries hfit tables s.val.memory ∧
      (foldTables width dimension count index entries hfit tables).Represents width base t.val.memory ∧
      Descriptor width dimension base sourceClock endpointClock diagonalClock t.val ∧
      Cursors dimension count (index+entries.length) t.val ∧ Workspace t.val ∧
      t.val.registers 46 = false ∧ Frame workBanks s.val t.val := by
  induction entries generalizing index s tables with
  | nil =>
    have hfalse : s.val.registers 46 = false := by simpa using htest
    refine ⟨1,s,by simp [foldPrice],Executes.done hfalse,?_,rfl,htables,hd,?_,hw,hfalse,Frame.refl _ _⟩
    · simp [SparseEmission.ReadGate.advance]
    · simpa using hc
  | cons e rest ih =>
    have hi : index < count := by simp only [List.length_cons] at hfit; omega
    have htrue : s.val.registers 46 = true := by
      have hnonempty := Count.wire_nonempty width e.val (rest.map Subtype.val)
      simpa only [recordsWire,List.map_cons,hnonempty,Bool.not_false] using htest
    obtain ⟨ac,a,acBound,ea,a110,asuffix,am,ae,ag,ad,ar,aw,af⟩ := Step.executes input randomTape
      width dimension count index base e.val sourceClock endpointClock diagonalClock (recordsWire width rest)
      s hi hcount hdimension e.property.1 e.property.2 hsep hd hc hw tables.endpoints tables.diagonal
      htables.endpoints htables.diagonal (by simpa only [recordsWire_cons] using hsource)
    let b := Count.peekState a
    have bd : Descriptor width dimension base sourceClock endpointClock diagonalClock b.val := ad.of_frame (peek_frame a)
    have br : Cursors dimension count (index+1) b.val := ⟨ar.left,ar.right,ar.mediator⟩
    have bw : Workspace b.val := ⟨aw.scratch,aw.sample,aw.packed,aw.payload,aw.shiftedColumn,aw.row,aw.column⟩
    have bt : (tables.next width dimension count index hi e).Represents width base b.val.memory := ⟨ae,ag⟩
    obtain ⟨rc,t,rcBound,et,t110,tm,tt,td,tr,tw,tfalse,tf⟩ := ih (index+1) b
      (by simp only [List.length_cons] at hfit; omega) bd br bw
      (tables.next width dimension count index hi e) bt asuffix (Count.peek_present a _ asuffix)
    refine ⟨1+(ac+3)+rc,t,?_,Executes.more htrue (ea.seq (Count.peek_executes input randomTape a)) et,
      ?_,?_,tt,td,?_,tw,tfalse,af.trans ((peek_frame a).trans tf)⟩
    · simp only [foldPrice]
      omega
    · rw [t110,show b.val.tapes 110 = a.val.tapes 110 from rfl,a110,SparseEmission.ReadGate.advance_add]
      simp only [recordsWire_cons,List.length_append,SparseEmission.entryWire_length]
    · rw [tm,show b.val.memory = a.val.memory from rfl,am]
      rfl
    · convert tr using 1
      simp only [List.length_cons]
      omega

theorem pass (input : List Bool) (randomTape : ℕ → Bool)
    (width dimension count index base : ℕ) (entries : List (BoundedEntry dimension))
    (sourceClock endpointClock diagonalClock : List Bool) (s : Store)
    (hfit : index+entries.length ≤ count) (hcount : count ≤ 3*dimension)
    (hdimension : dimension < 2^width) (hsep : 4*count*(width+3) ≤ base)
    (hd : Descriptor width dimension base sourceClock endpointClock diagonalClock s.val)
    (hc : Cursors dimension count index s.val) (hw : Workspace s.val)
    (tables : Tables dimension count) (htables : tables.Represents width base s.val.memory)
    (hsource : TapeRepresents (s.val.tapes 110) (recordsWire width entries)) :
    ∃ cost t, cost ≤ 3+foldPrice width dimension count index base diagonalClock entries hfit tables ∧
      Executes input randomTape passCode cost s t ∧
      t.val.tapes 110 = SparseEmission.ReadGate.advance (s.val.tapes 110) (recordsWire width entries).length ∧
      t.val.memory = foldMemory width dimension count index base entries hfit tables s.val.memory ∧
      (foldTables width dimension count index entries hfit tables).Represents width base t.val.memory ∧
      Descriptor width dimension base sourceClock endpointClock diagonalClock t.val ∧
      Cursors dimension count (index+entries.length) t.val ∧ Workspace t.val ∧
      t.val.registers 46 = false ∧ Frame workBanks s.val t.val := by
  obtain ⟨cost,t,hcost,he,ts,tm,tt,td,tc,tw,th,tf⟩ := executes input randomTape
    width dimension count index base entries sourceClock endpointClock diagonalClock (Count.peekState s)
    hfit hcount hdimension hsep (hd.of_frame (peek_frame s)) ⟨hc.left,hc.right,hc.mediator⟩
    ⟨hw.scratch,hw.sample,hw.packed,hw.payload,hw.shiftedColumn,hw.row,hw.column⟩
    tables htables hsource (Count.peek_present s _ hsource)
  exact ⟨3+cost,t,by omega,(Count.peek_executes input randomTape s).seq he,
    ts,tm,tt,td,tc,tw,th,(peek_frame s).trans tf⟩

end Maxwell.Cost.PositiveGraph.Loop
