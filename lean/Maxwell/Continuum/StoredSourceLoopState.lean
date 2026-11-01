import Maxwell.Continuum.StoredSourceStep
import Maxwell.Cost.LogRats

/-! The source traversal invariant carries actual archived input records,
packed geometry, and bounded rational work words. -/
namespace Maxwell.Continuum.SourcePayload
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalDataflow
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

structure Plan (n : ℕ) where
  data : Vector ℕ n
  base : ℕ
  slotWidth : ℕ
  geometryWidth : ℕ
  bankWidth : ℕ
  clock : List Bool
  constants : ℕ→ℕ
  source : List ℚ
  precision : ℕ
  scalar : ℚ
  template : List Bool
  slotPositive : 0<slotWidth
  slotBound : slotWidth≤geometryWidth
  clockLength : clock.length=slotWidth
  countWidth : n.bits.length≤geometryWidth
  fits : ∀i,(data.get i).bits.length≤slotWidth
  baseValue : constants 960=base
  widthValue : constants 961=slotWidth
  oneValue : constants 970=1
  bankWidth_two : 2≤bankWidth
  powerWidth : (2^precision).bits.length≤bankWidth
  precisionWidth : precision.bits.length≤bankWidth
  numeratorWidth : ∀q∈source,q.num.natAbs.bits.length≤bankWidth
  denominatorWidth : ∀q∈source,q.den.bits.length≤bankWidth
  span : 3*source.length≤n
  coordinates : ∀j<source.length,∀k,(GeometryOutput.terminalCoordinate data constants (3*j) k).bits.length≤geometryWidth

def archivePrefix (xs : List ℚ) (j : ℕ) : List Bool:=LogRats.records (xs.take j)

theorem archive_split (xs : List ℚ) (j : ℕ) (hj : j<xs.length) :
    LogRats.records xs=archivePrefix xs j++(Codec.rat xs[j]++LogRats.records (xs.drop (j+1))) := by
  calc
    LogRats.records xs=LogRats.records (xs.take j++xs.drop j):=congrArg LogRats.records (List.take_append_drop j xs).symm
    _=archivePrefix xs j++(Codec.rat xs[j]++LogRats.records (xs.drop (j+1))):=by
      rw [List.drop_eq_getElem_cons hj]
      simp only [LogRats.records,archivePrefix,List.flatMap_append,List.flatMap_cons]

theorem prefix_succ (xs : List ℚ) (j : ℕ) (hj : j<xs.length) :
    archivePrefix xs (j+1)=archivePrefix xs j++Codec.rat xs[j] := by
  simp only [archivePrefix,List.take_succ_eq_append_getElem hj,LogRats.records,
    List.flatMap_append,List.flatMap_singleton]

def rowBits {n : ℕ} (p : Plan n) (j : ℕ) : List Bool:=
  GeometryOutput.terminalBits p.data p.constants (3*j)++
    payloadBits p.precision (roundDyadic p.precision (p.source[j]?.getD 0*p.scalar)).numerator p.template

def stepCost {n : ℕ} (p : Plan n) : ℕ:=
  2^30*(p.geometryWidth+3)^2+(2^200*(p.precision+p.bankWidth+8)^2+10*p.template.length)

structure State {n : ℕ} (p : Plan n) (j : ℕ) (gv : ℕ→ℕ) (v : ℕ→Parts) (s : Store) : Prop where
  geometry : GeometryOutput.Context p.data p.base p.slotWidth p.geometryWidth p.clock p.constants gv s
  cursor : gv 971=3*j
  raw : Ready bank v s
  width : WidthBank bank p.bankWidth v
  good : Good bank v
  multiplier : (v 13).value=p.scalar
  clean : DyadicFloor.Clean s.val
  power : Word s.val 144 (2^p.precision)
  precision : Word s.val 4427 p.precision
  template : BankArray.Word s.val 992 p.template
  archive : ∃origin:ℤ,s.val.tapes 85=BitTape.translate origin
    (NormalizedRecordParser.cursor (LogRats.records p.source) (archivePrefix p.source j).length)
  old : WordCleanup.Bounded parseWords p.bankWidth s.val

theorem State.count_frame {n j : ℕ} {p : Plan n} {gv : ℕ→ℕ} {v : ℕ→Parts} {s t : Store}
    (h : State p j gv v s) (f : CountedShifted.Frame 972 s t) : State p j gv v t := by
  have keep (i : ℕ) (hi : i≠972):=f.2.2.2.2.2.1 i hi
  refine ⟨h.geometry.count_frame 972 (by decide) f,h.cursor,?_,h.width,h.good,h.multiplier,?_,
    word_of_eq (keep 144 (by decide)) h.power,word_of_eq (keep 4427 (by decide)) h.precision,
    BankArray.word_of_eq (keep 992 (by decide)) h.template,?_,?_⟩
  · refine ⟨?_,?_⟩
    · intro i hi
      exact word_of_eq (keep i (by intro he;subst i;exact (by decide : 972∉ids bank) hi)) (h.raw.1 i hi)
    · intro i hi
      exact blank_of_eq (keep i (by omega)) (h.raw.2 i hi)
  · refine ⟨blank_of_eq (keep 4 (by decide)) h.clean.1,?_⟩
    intro i hi
    have hn : i≠972:=by
      simp only [DyadicFloor.extraIds,NaturalQuotient.workPorts,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hi
      omega
    exact blank_of_eq (keep i hn) (h.clean.2 i hi)
  · obtain ⟨origin,archive⟩:=h.archive
    exact ⟨origin,(keep 85 (by decide)).trans archive⟩
  · intro i hi
    obtain ⟨xs,hxs,word⟩:=h.old i hi
    exact ⟨xs,hxs,BankArray.word_of_eq (keep i (by
      simp only [parseWords,List.mem_cons,List.not_mem_nil,or_false] at hi;omega)) word⟩

theorem State.step {n j : ℕ} {p : Plan n} {gv : ℕ→ℕ} {v : ℕ→Parts} {s : Store}
    (h : State p j gv v s) (hj : j<p.source.length) (input : List Bool) (tape : ℕ→Bool) :
    ∃cost t w,Executes input tape stepCode cost s t ∧cost≤stepCost p ∧
      State p (j+1) w (resetValues v) t ∧
      t.val.output=(rowBits p j).reverse++s.val.output ∧GeometryOutput.OutputFrame stepWork s.val t.val := by
  obtain ⟨archiveOrigin,archiveStored⟩:=h.archive
  have qmem : p.source[j]∈p.source:=List.getElem_mem hj
  obtain ⟨cost,t,w,ex,hc,out,g,index,raw,width,good,clean,power,archive,old,frame⟩:=step_executes h.geometry
    p.slotPositive p.slotBound p.clockLength p.countWidth p.fits p.baseValue p.widthValue p.oneValue
    (by rw [h.cursor];have hh:=p.span;omega) (by rw [h.cursor];exact p.coordinates j hj)
    p.precision p.bankWidth p.bankWidth_two p.powerWidth p.precisionWidth p.source[j] v h.width h.good
    (p.numeratorWidth _ qmem) (p.denominatorWidth _ qmem) p.template input tape archiveOrigin
    (archivePrefix p.source j) (LogRats.records (p.source.drop (j+1))) h.raw h.old
    (by rw [←archive_split p.source j hj];exact archiveStored) h.clean h.power h.precision h.template
  refine ⟨cost,t,w,ex,hc,⟨g,?_,raw,width,good,?_,clean,power,
    word_of_eq (frame.tapes 4427 (by decide)) h.precision,
    BankArray.word_of_eq (frame.tapes 992 (by decide)) h.template,?_,old⟩,?_,frame⟩
  · rw [index,h.cursor];omega
  · simpa [resetValues,resetSlots] using h.multiplier
  · refine ⟨archiveOrigin,?_⟩
    rw [←archive_split p.source j hj] at archive
    simpa only [prefix_succ p.source j hj,List.length_append,Nat.cast_add] using archive
  · rw [out,h.cursor]
    simp only [rowBits,numerator,Function.update_self,Parts.literal_value,
      Function.update_of_ne (by decide : (13:ℕ)≠0),h.multiplier,List.getElem?_eq_getElem hj,Option.getD_some]

#print axioms State.step
end Maxwell.Continuum.SourcePayload
