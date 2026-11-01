import Maxwell.Continuum.RationalDataflowTablePromote
import Maxwell.Continuum.StoredWellPayload
import Maxwell.Continuum.StoredGeometryState
import Maxwell.Continuum.WellStrengthPassState
import Maxwell.Cost.Structured.WordLiteral
import Maxwell.Cost.BankArray.Frame

/-! The actual table descriptors move to the serializer ports, and its
cursor and increment word are initialized by charged machine operations. -/
namespace Maxwell.Continuum.RationalDataflow.WellStrengthPass
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
open PartArray
set_option maxHeartbeats 5000000
set_option maxRecDepth 16384

def handoffCode : Code := .seq promoteCode (.seq (WordLiteral.code 728 0) (WordLiteral.code 727 1))
def handoffIds : Finset ℕ := {200,202,203,204,205,727,728}

theorem handoffIds_range (k : ℕ) (hk : k∈handoffIds) : 200 ≤ k ∧ k<960 := by
  simp only [handoffIds,Finset.mem_insert,Finset.mem_singleton] at hk
  omega

theorem handoff_rational_frame {S : Finset ℕ} {v : ℕ→Parts} {s t : Store}
    (h : Ready S v s) (f : BinaryPrecision.Frame handoffIds s.val t.val) : Ready S v t := by
  constructor
  · intro k hk
    exact word_of_eq (f.tapes k (by
      intro he
      have range := handoffIds_range k he
      exact outside_workspace S k (by omega) (Finset.mem_union_right _ hk))) (h.1 k hk)
  · intro k hk
    exact blank_of_eq (f.tapes k (by intro he;have range:=handoffIds_range k he;omega)) (h.2 k hk)

theorem handoff_geometry_frame {n base width B : ℕ} {data : Vector ℕ n} {clock : List Bool}
    {constants gv : ℕ→ℕ} {s t : Store}
    (g : GeometryOutput.Context data base width B clock constants gv s)
    (f : BinaryPrecision.Frame handoffIds s.val t.val) :
    GeometryOutput.Context data base width B clock constants gv t := by
  have keep (k : ℕ) (hk : k<10) := f.tapes k (by intro he;have range:=handoffIds_range k he;omega)
  refine ⟨⟨?_,g.ready.scratch.of_tapes keep,blank_of_eq (keep 7 (by decide)) g.ready.seven⟩,
    g.wordWidth,by simpa only [f.memory] using g.array,
    BankArray.word_of_eq (f.tapes 962 (by decide)) g.clockWord,g.fixed⟩
  intro k hk
  have ge := GeometryOutput.ids_ge k hk
  exact word_of_eq (f.tapes k (by intro he;have range:=handoffIds_range k he;omega)) (g.ready.bank k hk)

theorem State.serializer_ready {J P index : ℕ} {a : Table J} {v : ℕ→Parts} {s : Store}
    (h : State a P v index s) : Ready StoredInteger.slots v s :=
  ⟨fun k hk=>h.rational.1 k ((by decide : ids StoredInteger.slots⊆ids WellStrength.bank) hk),h.rational.2⟩

theorem canonical_serializer_width (v : ℕ→Parts) (canonical : WellStrengthReset.canonical v=v)
    (B : ℕ) (hB : 1 ≤ B) : WidthBank StoredInteger.slots B v := by
  have zero : v 0=Parts.literal 0 := by
    have he := congrFun canonical 0
    simpa [WellStrengthReset.canonical,resetList_values,WellStrengthReset.targets] using he.symm
  intro i hi
  have he : i=0 := by simpa only [StoredInteger.slots,Finset.mem_singleton] using hi
  rw [he,zero]
  exact (Parts.literal_width RationalWords.width_zero').mono hB

theorem handoff_executes {J P B : ℕ} (a : Table J) (hm : a.MetadataWidth B)
    (v : ℕ→Parts) (hw : WidthBank StoredInteger.slots B v)
    (old : ℕ→List Bool) (lengths : ∀i∈inputHeaderIds,(old i).length ≤ B)
    (indexOld oneOld profile template : List Bool) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hr : Ready StoredInteger.slots v s) (ha : a.OutputReady s)
    (headers : ∀i∈inputHeaderIds,BankArray.Word s.val i (old i))
    (index : BankArray.Word s.val 728 indexOld) (one : BankArray.Word s.val 727 oneOld)
    (precision : Word s.val 990 P) (profileWord : BankArray.Word s.val 991 profile)
    (templateWord : BankArray.Word s.val 992 template) :
    ∃cost t,Executes input tape handoffCode cost s t ∧
      cost ≤ 105*B+6*(indexOld.length+oneOld.length)+138 ∧
      WellPayload.State a P B 0 profile template v t ∧
      BinaryPrecision.Frame handoffIds s.val t.val := by
  obtain ⟨c,u,e0,hc,a0,f0⟩ := ha.promote a hm old lengths input tape s headers
  obtain ⟨w,e1,index1,f1⟩ := WordLiteral.executes 728 0 input tape indexOld u
    (BankArray.word_of_eq (f0.tapes 728 (by decide)) index)
  obtain ⟨t,e2,one2,f2⟩ := WordLiteral.executes 727 1 input tape oneOld w
    (BankArray.word_of_eq ((f1.tapes 727 (by decide)).trans (f0.tapes 727 (by decide))) one)
  have tailFrame : BinaryPrecision.Frame ({727,728}:Finset ℕ) u.val t.val :=
    (f1.mono (by decide)).trans (f2.mono (by decide))
  have frame : BinaryPrecision.Frame handoffIds s.val t.val :=
    (f0.mono (by decide)).trans (tailFrame.mono (by decide))
  have keep (k : ℕ) (hk : k<10) := tailFrame.tapes k (by
    simp only [Finset.mem_insert,Finset.mem_singleton];omega)
  have tableFinal : a.Ready t := a0.transfer tailFrame.memory (fun k hk=>tailFrame.tapes k (by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    simp only [Finset.mem_insert,Finset.mem_singleton];omega))
    (a0.scratch.of_tapes keep) (blank_of_eq (keep 7 (by decide)) a0.seven)
  refine ⟨c+((6*indexOld.length+10*(0:ℕ).bits.length+11)+(6*oneOld.length+10*(1:ℕ).bits.length+11)),
    t,e0.seq (e1.seq e2),?_,⟨handoff_rational_frame hr frame,hw,tableFinal,
      word_of_eq (f2.tapes 728 (by decide)) index1,one2,
      word_of_eq (frame.tapes 990 (by decide)) precision,
      BankArray.word_of_eq (frame.tapes 991 (by decide)) profileWord,
      BankArray.word_of_eq (frame.tapes 992 (by decide)) templateWord⟩,frame⟩
  change c+((6*indexOld.length+10*0+11)+(6*oneOld.length+10*1+11)) ≤ _
  omega

#print axioms handoff_executes
end Maxwell.Continuum.RationalDataflow.WellStrengthPass
