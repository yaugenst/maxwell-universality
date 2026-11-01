import Maxwell.Continuum.CalibrationSchurGather
import Maxwell.Continuum.CalibrationInverseOutputCleanup
import Maxwell.Continuum.CalibrationSchurColumn

/-! The completed integer inverse feeds an actual Schur column: compute its
common denominator power, gather the required144 entries, retire the array
scratch, and execute the24 rational row expressions. -/
namespace Maxwell.Continuum.Calibration.SchurReadColumn
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.CalibrationMatrix RationalDataflow FreeFiber
open NeumannMachine
set_option maxHeartbeats 6000000
set_option maxRecDepth 16384

def rows : List (Fin 24) := List.finRange 24
def code (column : Fin 24) : Code := .seq OutputPrepare.code
  (.seq (OutputGather.code SchurGather.requests)
    (.seq OutputCleanup.code (SchurColumn.code column rows)))
def inputWidth (D N : ℕ) : ℕ := D.bits.length+N.bits.length+3
def workingWidth (D N B : ℕ) : ℕ := B+(N+1)*D.bits.length+1+SchurColumn.literalBudget
def readoutWords : List ℕ := 140::List.range' 530 5
def readoutWidth (D N B : ℕ) : ℕ := workingWidth D N B+OutputGather.indexWidth SchurGather.requests (inputWidth D N)
def costBound (D N B C : ℕ) : ℕ :=
  DenominatorPower.costBound N (OutputPrepare.width D N C)+
    (OutputGather.costBound SchurGather.requests (inputWidth D N) (workingWidth D N B)+
      (OutputCleanup.costBound (workingWidth D N B)+SchurColumn.costBound rows (workingWidth D N B)))
def result {N : ℕ} (a : Snapshot (aliasArraySize (N+3))) (D : ℕ)
    (column : Fin 24) (p : ℕ→Parts) : ℕ→Parts :=
  SchurColumn.values column rows (OutputGather.parts a (D^(N+1)) SchurGather.requests p)

attribute [local irreducible] SchurColumn.literalBudget SchurRow.nodeCount

theorem result_keep {N : ℕ} (a : Snapshot (aliasArraySize (N+3))) (D : ℕ)
    (column : Fin 24) (p : ℕ→Parts) (i : ℕ) (outside : i<240 ∨ 384 ≤ i)
    (low : i<1200) (unused : ∀row,i≠SchurRow.output row column) : result a D column p i=p i := by
  rw [result,SchurColumn.values_keep column rows _ i low (fun row _=>unused row)]
  apply OutputGather.parts_keep
  intro r hr
  have bounds:=SchurGather.targets r hr
  omega

theorem index_width (D N : ℕ) :
    ∀k∈OutputPrepare.indexIds,(OutputPrepare.indexNumbers D N k).bits.length≤ inputWidth D N := by
  intro k _
  unfold OutputPrepare.indexNumbers
  split_ifs
  · unfold inputWidth;omega
  · unfold inputWidth;omega
  · change 1≤ inputWidth D N
    unfold inputWidth;omega
  · exact Nat.zero_le _

theorem executes (column : Fin 24) (N D B C : ℕ) (a : Snapshot (aliasArraySize (N+3)))
    (work : ℕ→ℕ) (p : ℕ→Parts) (positive:0<D)
    (size:a.data.Sized B) (hw:∀k∈Finset.Icc 530 534,(work k).bits.length≤C)
    (pw:WidthBank SchurRow.bank B p) (good:Good SchurRow.bank p)
    (decoded:∀i:Fin (aliasArraySize (N+3)),((Horner.channels a.words 10 11).value i:ℚ)/(D:ℚ)^(N+1)=
      (cachedInverseApply (p 232).value (p 233).value (fun j=>(p (234+j.val)).value) (N+3)
        (rationalRightCoupling (rationalBasisField column)) (N+1)).get i)
    (input : List Bool) (tape : ℕ→Bool) (count : List Bool) (s : Store)
    (ready:a.Ready count B s.val) (denominator:RationalAccumulator.Word s.val 126 D)
    (counter:RationalAccumulator.Word s.val 304 N)
    (working:NatAssign.Bank (Finset.Icc 530 534) work s.val)
    (index:RationalAccumulator.Blank s.val 140) (blank105:RationalAccumulator.Blank s.val 105)
    (cells:Cells SchurRow.bank p s.val) :
    ∃cost t,Executes input tape (code column) cost s t ∧ cost≤costBound D N B C ∧
      Ready SchurRow.bank (result a D column p) t ∧ Good SchurRow.bank (result a D column p) ∧
      WidthBank SchurRow.bank (SchurColumn.resultWidth rows (workingWidth D N B)) (result a D column p) ∧
      (∀row,(result a D column p (SchurRow.output row column)).value=
        cachedSchurMatrix (p 232).value (p 233).value (fun j=>(p (234+j.val)).value) (N+1) row column) ∧
      (∀k,1000 ≤ k→k∉ports SchurRow.bank→t.val.tapes k=s.val.tapes k) ∧
      (∀k,(k=4 ∨ k=37 ∨ 107 ≤ k)→k<1000→k≠140→(k<530 ∨ 534<k)→t.val.tapes k=s.val.tapes k) ∧
      WordCleanup.Bounded readoutWords (readoutWidth D N B) t.val ∧
      BankArray.Scratch t.val ∧ RationalAccumulator.Blank t.val 7 ∧
      (∀i,(i<240 ∨ 384 ≤ i)→i<1200→(∀row,i≠SchurRow.output row column)→
        result a D column p i=p i) := by
  let W:=workingWidth D N B
  have bw:B≤W:=by unfold W workingWidth;omega
  have large:SchurColumn.literalBudget≤W:=by unfold W workingWidth;omega
  have powerWidth:(D^(N+1)).bits.length≤W:=
    (DenominatorPower.denominator_width D N D.bits.length le_rfl).trans (by unfold W workingWidth;omega)
  have sizeW:a.data.Sized W:=by
    rcases size with ⟨h1,h2,h3,h4,h5,h6,h7⟩
    exact ⟨h1.trans bw,h2.trans bw,h3.trans bw,h4.trans bw,fun i=>(h5 i).trans bw,h6.trans bw,h7.trans bw⟩
  obtain ⟨c0,u,e0,b0,state0,index0,frame0⟩:=
    OutputPrepare.executes a count B D N C work hw input tape s ready denominator counter working index
  have cells0:Cells SchurRow.bank p u.val:=cells.transfer (by
    intro k hk
    apply frame0.tapes
    simp only [DenominatorPower.changed,Finset.mem_insert,Finset.mem_singleton]
    omega)
  have cold0:=OutputCleanup.cold_prepare (OutputCleanup.cold_bounded a count s.val ready blank105) frame0
  have pwW:WidthBank SchurRow.bank W p:=fun i hi=>(pw i hi).mono bw
  obtain ⟨c1,v,e1,b1,state1,index1,indexWidth1,readWidth,_,cells1,pw1,_,_,_,_,cold1,high1,middle1⟩:=
    OutputGather.executes SchurGather.requests N (D^(N+1)) (inputWidth D N) W a SchurRow.bank
      (OutputPrepare.indexNumbers D N) (fun _=>0) p (by unfold inputWidth;omega) sizeW powerWidth
      (index_width D N) (by intro k _;simp) (by simp [OutputPrepare.indexNumbers])
      (by intro r hr;exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_Ico.mpr ⟨by have h:240≤r.target:=(SchurGather.targets r hr).1;omega,(SchurGather.targets r hr).2⟩)))
      pwW input tape u (OutputPoint.initial state0) index0 cells0
  have coldW:WordCleanup.Bounded OutputCleanup.coldWords W v.val:=by
    have cold:=OutputCleanup.cold_transfer cold0 cold1
    intro k hk
    obtain ⟨bits,width,word⟩:=cold k hk
    exact ⟨bits,width.trans bw,word⟩
  obtain ⟨c2,w,e2,b2,ready2,frame2⟩:=OutputCleanup.executes a SchurRow.bank _ _ W sizeW readWidth
    input tape v state1 coldW cells1
  have good2:=OutputGather.parts_good a SchurGather.requests SchurRow.bank p (pow_pos positive (N+1)) good
  obtain ⟨c3,t,e3,b3,ready3,good3,width3,values3,frame3⟩:=
    SchurColumn.executes column rows _ W large pw1 good2 input tape w ready2
  have retained (k : ℕ) (hk : 1000 ≤ k) (outside : k∉ports SchurRow.bank) :
      t.val.tapes k=s.val.tapes k := by
    have outsideWork : k∉workspace SchurRow.bank := by
      simp only [workspace,ids,Finset.mem_union,not_or]
      refine ⟨?_,outside,?_⟩
      · simp only [Finset.mem_insert,Finset.mem_singleton];omega
      · simp only [workPorts,temporaryPorts,RationalMagnitude.ids,Finset.mem_union,
          Finset.mem_insert,Finset.mem_singleton];omega
    apply (frame3.tapes k outsideWork).trans
    apply (frame2.tapes k ?_).trans
    · apply (high1 k (by omega) ?_).trans
      · apply frame0.tapes
        simp only [DenominatorPower.changed,Finset.mem_insert,Finset.mem_singleton]
        omega
      · intro r hr cell
        apply outside
        apply Finset.mem_biUnion.mpr
        refine ⟨r.target,?_,cell⟩
        exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_Ico.mpr ⟨by have h:240≤r.target:=(SchurGather.targets r hr).1;omega,
            (SchurGather.targets r hr).2⟩))
    · simp only [OutputCleanup.clearWords,List.toFinset_cons,List.toFinset_nil,
        Finset.mem_insert,Finset.notMem_empty,or_false]
      omega
  have middle (k : ℕ) (lo : k=4 ∨ k=37 ∨ 107 ≤ k) (hi : k<1000) (ne : k≠140) (outside : k<530 ∨ 534<k) : t.val.tapes k=s.val.tapes k := by
    apply (frame3.tapes k ?_).trans
    · apply (frame2.tapes k ?_).trans
      · apply (middle1 k lo hi ne outside).trans
        apply frame0.tapes
        simp only [DenominatorPower.changed,Finset.mem_insert,Finset.mem_singleton];omega
      · simp only [OutputCleanup.clearWords,List.toFinset_cons,List.toFinset_nil,
          Finset.mem_insert,Finset.notMem_empty,or_false];omega
    · simp only [workspace,ids,Finset.mem_union,not_or]
      refine ⟨?_,?_,?_⟩
      · simp only [Finset.mem_insert,Finset.mem_singleton];omega
      · intro h
        obtain ⟨i,_,cell⟩:=Finset.mem_biUnion.mp h
        simp only [cellPorts,positivePort,negativePort,denominatorPort,
          Finset.mem_insert,Finset.mem_singleton] at cell
        omega
      · simp only [workPorts,temporaryPorts,RationalMagnitude.ids,Finset.mem_union,
          Finset.mem_insert,Finset.mem_singleton];omega
  have after (k : ℕ) (hk : k∈({5,6,7,8,9,140,530,531,532,533,534}:Finset ℕ)) :
      t.val.tapes k=v.val.tapes k := by
    have cases := hk
    simp only [Finset.mem_insert,Finset.mem_singleton] at cases
    apply (frame3.tapes k ?_).trans (frame2.tapes k ?_)
    · simp only [workspace,ids,Finset.mem_union,not_or]
      refine ⟨by simp only [Finset.mem_insert,Finset.mem_singleton];omega,?_,?_⟩
      · intro h
        obtain ⟨i,_,cell⟩:=Finset.mem_biUnion.mp h
        simp only [cellPorts,positivePort,negativePort,denominatorPort,
          Finset.mem_insert,Finset.mem_singleton] at cell
        omega
      · simp only [workPorts,temporaryPorts,RationalMagnitude.ids,Finset.mem_union,
          Finset.mem_insert,Finset.mem_singleton];omega
    · simp only [OutputCleanup.clearWords,List.toFinset_cons,List.toFinset_nil,
        Finset.mem_insert,Finset.notMem_empty,or_false];omega
  have readout : WordCleanup.Bounded readoutWords (readoutWidth D N B) t.val := by
    intro k hk
    have cases : k=140 ∨ (530≤k ∧ k<535) := by
      simpa only [readoutWords,List.mem_cons,List.mem_range'_1] using hk
    have member : k∈({5,6,7,8,9,140,530,531,532,533,534}:Finset ℕ) := by
      simp only [Finset.mem_insert,Finset.mem_singleton];omega
    by_cases eq:k=532
    · subst k
      exact ⟨(D^(N+1)).bits,powerWidth.trans (Nat.le_add_right _ _),
        BankArray.word_of_eq (after 532 member) state1.denominator⟩
    · have hi:k∈OutputPrepare.indexIds := by
        simp only [OutputPrepare.indexIds,Finset.mem_insert,Finset.mem_singleton];omega
      exact ⟨_,(indexWidth1 k hi).trans (Nat.le_add_left _ _),
        BankArray.word_of_eq (after k member) (index1 k hi)⟩
  have scratch : BankArray.Scratch t.val :=
    ⟨ready3.2 0 (by decide),ready3.2 1 (by decide),ready3.2 2 (by decide),ready3.2 3 (by decide),
      RationalAccumulator.blank_of_eq (after 5 (by decide)) state1.scratch.2.2.2.2.1,
      RationalAccumulator.blank_of_eq (after 6 (by decide)) state1.scratch.2.2.2.2.2.1,
      RationalAccumulator.blank_of_eq (after 8 (by decide)) state1.scratch.2.2.2.2.2.2.1,
      RationalAccumulator.blank_of_eq (after 9 (by decide)) state1.scratch.2.2.2.2.2.2.2⟩
  refine ⟨c0+(c1+(c2+c3)),t,e0.seq (e1.seq (e2.seq e3)),
    Nat.add_le_add b0 (Nat.add_le_add b1 (Nat.add_le_add b2 b3)),ready3,good3,width3,?_,retained,middle,readout,scratch,
    RationalAccumulator.blank_of_eq (after 7 (by decide)) state1.seven,
    result_keep a D column p⟩
  intro row
  rw [show (result a D column p (SchurRow.output row column)).value=
      (SchurExpression.expression row column).evaluate
        (valueBank (OutputGather.parts a (D^(N+1)) SchurGather.requests p)) from values3 row (by simp [rows])]
  let gathered:=OutputGather.parts a (D^(N+1)) SchurGather.requests p
  have keep (i : ℕ) (hi:i<240) : (gathered i).value=(p i).value:=by
    dsimp only [gathered]
    rw [SchurGather.scalar_kept a p i hi]
  have quasi:(fun j : Fin 3=>(gathered (234+j.val)).value)=(fun j : Fin 3=>(p (234+j.val)).value):=by
    funext j
    exact keep _ (by omega)
  have vec:Vector.ofFn (fun i=>((Horner.channels a.words 10 11).value i:ℚ)/(D^(N+1):ℕ))=
      cachedInverseApply (p 232).value (p 233).value (fun j=>(p (234+j.val)).value) (N+3)
        (rationalRightCoupling (rationalBasisField column)) (N+1):=by
    apply Vector.ext
    intro i hi
    change (Vector.ofFn _).get ⟨i,hi⟩=(cachedInverseApply (p 232).value (p 233).value
      (fun j=>(p (234+j.val)).value) (N+3) (rationalRightCoupling (rationalBasisField column)) (N+1)).get ⟨i,hi⟩
    simpa only [vector_get_ofFn,Nat.cast_pow] using decoded ⟨i,hi⟩
  have h:=SchurExpression.cached_value row column N (valueBank gathered) (by
    intro j plus
    change (gathered (SchurExpression.neighborRegister row j plus)).value=_
    rw [SchurGather.retained_value,vec]
    simp only [valueBank,keep 232 (by decide),keep 233 (by decide),quasi])
  simpa only [valueBank,keep 232 (by decide),keep 233 (by decide),quasi] using h

theorem executes_radius (column : Fin 24) (R D B C : ℕ) (a : Snapshot (aliasArraySize R))
    (work : ℕ→ℕ) (p : ℕ→Parts) (radius : 3 ≤ R) (positive : 0 < D)
    (size : a.data.Sized B) (hw : ∀k∈Finset.Icc 530 534,(work k).bits.length ≤ C)
    (pw : WidthBank SchurRow.bank B p) (good : Good SchurRow.bank p)
    (decoded : ∀i:Fin (aliasArraySize R),((Horner.channels a.words 10 11).value i:ℚ)/(D:ℚ)^(R-2)=
      (cachedInverseApply (p 232).value (p 233).value (fun j=>(p (234+j.val)).value) R
        (rationalRightCoupling (rationalBasisField column)) (R-2)).get i)
    (input : List Bool) (tape : ℕ→Bool) (count : List Bool) (s : Store)
    (ready : a.Ready count B s.val) (denominator : RationalAccumulator.Word s.val 126 D)
    (counter : RationalAccumulator.Word s.val 304 (R-3))
    (working : NatAssign.Bank (Finset.Icc 530 534) work s.val)
    (index : RationalAccumulator.Blank s.val 140) (blank105 : RationalAccumulator.Blank s.val 105)
    (cells : Cells SchurRow.bank p s.val) :
    ∃cost t out,Executes input tape (code column) cost s t ∧ cost ≤ costBound D (R-3) B C ∧
      Ready SchurRow.bank out t ∧ Good SchurRow.bank out ∧
      WidthBank SchurRow.bank (SchurColumn.resultWidth rows (workingWidth D (R-3) B)) out ∧
      (∀row,(out (SchurRow.output row column)).value=
        cachedSchurMatrix (p 232).value (p 233).value (fun j=>(p (234+j.val)).value) (R-2) row column) ∧
      (∀k,1000 ≤ k→k∉ports SchurRow.bank→t.val.tapes k=s.val.tapes k) ∧
      (∀k,(k=4 ∨ k=37 ∨ 107 ≤ k)→k<1000→k≠140→(k<530 ∨ 534<k)→t.val.tapes k=s.val.tapes k) ∧
      WordCleanup.Bounded readoutWords (readoutWidth D (R-3) B) t.val ∧
      BankArray.Scratch t.val ∧ RationalAccumulator.Blank t.val 7 ∧
      (∀i,(i<240 ∨ 384 ≤ i)→i<1200→(∀row,i≠SchurRow.output row column)→ out i=p i) := by
  obtain ⟨N, rfl⟩ : ∃N,R=N+3 := ⟨R-3,(Nat.sub_add_cancel radius).symm⟩
  have steps : N+3-2=N+1 := by omega
  simp only [Nat.add_sub_cancel,steps] at decoded counter ⊢
  obtain ⟨cost,t,execution,charge,output,valid,width,value,frame,middle,readout,scratch,seven,kept⟩ := executes column N D B C a work p
    positive size hw pw good decoded input tape count s ready denominator counter working index blank105 cells
  exact ⟨cost,t,result a D column p,execution,charge,output,valid,width,value,frame,middle,readout,scratch,seven,kept⟩

#print axioms executes
#print axioms executes_radius
end Maxwell.Continuum.Calibration.SchurReadColumn
