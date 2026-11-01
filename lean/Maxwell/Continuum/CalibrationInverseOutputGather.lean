import Maxwell.Continuum.CalibrationInverseOutputCapture
import Maxwell.Continuum.RationalDataflowRetainedCells

/-! A fixed list of inverse entries is read using computed addresses and copied
into raw rational cells. The Horner descriptors remain live until every read
has completed; no arithmetic scratch bank is assumed during this phase. -/
namespace Maxwell.Continuum.Calibration.NeumannMachine.OutputGather
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.CalibrationMatrix RationalDataflow FreeFiber
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

structure Request where
  point : Alias
  bounds : ∀j,|point j|≤2
  polarization : Fin 3
  target : ℕ

def Request.index (r : Request) (N : ℕ) : Fin (aliasArraySize (N+3)) :=
  OutputIndex.index N r.point r.bounds r.polarization
def Request.parts (r : Request) {N : ℕ} (a : Snapshot (aliasArraySize (N+3))) (D : ℕ) : Parts :=
  OutputRead.entryParts a D (r.index N)
def Request.code (r : Request) : Code :=
  .seq (OutputPoint.code r.point r.polarization) (StoredParts.restoreCode 30 r.target)
def nextWidth (A : ℕ) : ℕ := 2^19*(A+1)
def stepCost (A B : ℕ) : ℕ := OutputPoint.costBound A B+63*(B+1)

theorem count_kept (r : Request) (v : ℕ→ℕ) :
    NatAssign.values (OutputIndex.plan r.point r.polarization) v 304=v 304 := by
  simp [OutputIndex.plan,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,Function.update_of_ne]

theorem Request.executes (r : Request) (N D A B : ℕ) (a : Snapshot (aliasArraySize (N+3)))
    (S : Finset ℕ) (n v : ℕ→ℕ) (p : ℕ→Parts)
    (hA:3≤A) (size:a.data.Sized B) (denWidth:D.bits.length≤B)
    (indexWidth:∀k∈OutputPrepare.indexIds,(n k).bits.length≤A)
    (valueWidth:∀k∈OutputRead.ids,(v k).bits.length≤B) (count:n 304=N)
    (target:r.target∈S) (partsWidth:WidthBank S B p)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (state:OutputPoint.State a D v s.val)
    (indexBank:NatAssign.Bank OutputPrepare.indexIds n s.val) (cells:Cells S p s.val) :
    let nf:=NatAssign.values (OutputIndex.plan r.point r.polarization) n
    let vf:=OutputRead.values a D (r.index N) v
    let pf:=Function.update p r.target (r.parts a D)
    ∃cost t, Executes input tape r.code cost s t ∧ cost≤stepCost A B ∧
      OutputPoint.State a D vf t.val ∧ NatAssign.Bank OutputPrepare.indexIds nf t.val ∧
      (∀k∈OutputPrepare.indexIds,(nf k).bits.length≤nextWidth A) ∧
      (∀k∈OutputRead.ids,(vf k).bits.length≤B) ∧ nf 304=N ∧
      Cells S pf t.val ∧ WidthBank S B pf ∧
      t.val.memory=s.val.memory ∧ t.val.inputHead=s.val.inputHead ∧
      t.val.randomCursor=s.val.randomCursor ∧ t.val.output=s.val.output ∧
      (∀k∈OutputPoint.coldIds,t.val.tapes k=s.val.tapes k) ∧
      (∀k,600 ≤ k→k∉cellPorts r.target→t.val.tapes k=s.val.tapes k) ∧
      (∀k,(k=4 ∨ k=37 ∨ 107 ≤ k)→k<1000→k≠140→(k<530 ∨ 534<k)→t.val.tapes k=s.val.tapes k) := by
  dsimp only
  obtain ⟨c0,u,e0,b0,state0,index0,iw,vw,_,mem0,head0,random0,out0,keep0,cold0,middle0⟩:=
    OutputPoint.executes N D A B r.point r.bounds r.polarization a n v hA size denWidth
      indexWidth valueWidth count input tape s state indexBank
  have cells0:Cells S p u.val:=cells.transfer (fun k hk=>keep0 k (by omega))
  have partWidth:(r.parts a D).Width B:=OutputPoint.entry_width state.stored size denWidth _
  obtain ⟨c1,t,e1,b1,state1,index1,cell1,frame1⟩:=
    OutputPoint.capture_executes a _ _ r.target (p r.target) (r.parts a D) B
      (partsWidth _ target) partWidth input tape u state0 index0 (cells0 _ target)
      (OutputPoint.entry_stored a _ v u.val state0.bank)
  refine ⟨c0+c1,t,e0.seq e1,Nat.add_le_add b0 b1,state1,index1,iw,vw,
    (count_kept r n).trans count,cells0.write cell1 frame1,?_,
    frame1.memory.trans mem0,frame1.inputHead.trans head0,
    frame1.randomCursor.trans random0,frame1.output.trans out0,?_,
    (fun k hk ho=>(frame1.tapes k ho).trans (keep0 k hk)),?_⟩
  · intro i hi
    by_cases eq:i=r.target
    · simpa only [eq,Function.update_self] using partWidth
    · simpa only [Function.update_of_ne eq] using partsWidth i hi
  · intro k hk
    have lo:k<1000:=by
      simp only [OutputPoint.coldIds,Finset.mem_insert,Finset.mem_singleton] at hk
      omega
    have hp:=positivePort_ge r.target
    have hn:=negativePort_ge r.target
    have hd:=denominatorPort_ge r.target
    apply (frame1.tapes k ?_).trans (cold0 k hk)
    simp only [cellPorts,Finset.mem_insert,Finset.mem_singleton]
    omega

  · intro k lo hi ne outside
    apply (frame1.tapes k ?_).trans (middle0 k lo hi ne outside)
    simp only [cellPorts,positivePort,negativePort,denominatorPort,Finset.mem_insert,Finset.mem_singleton]
    omega

def code : List Request→Code
  | [] => .skip
  | r::rest => .seq r.code (code rest)
def parts {N : ℕ} (a : Snapshot (aliasArraySize (N+3))) (D : ℕ) : List Request→(ℕ→Parts)→(ℕ→Parts)
  | [],p => p
  | r::rest,p => parts a D rest (Function.update p r.target (r.parts a D))
def indexValues : List Request→(ℕ→ℕ)→(ℕ→ℕ)
  | [],n => n
  | r::rest,n => indexValues rest (NatAssign.values (OutputIndex.plan r.point r.polarization) n)
def readValues {N : ℕ} (a : Snapshot (aliasArraySize (N+3))) (D : ℕ) : List Request→(ℕ→ℕ)→(ℕ→ℕ)
  | [],v => v
  | r::rest,v => readValues a D rest (OutputRead.values a D (r.index N) v)
def indexWidth : List Request→ℕ→ℕ
  | [],A => A
  | _::rest,A => indexWidth rest (nextWidth A)
def costBound : List Request→ℕ→ℕ→ℕ
  | [],_,_ => 1
  | _::rest,A,B => stepCost A B+costBound rest (nextWidth A) B

theorem executes (requests : List Request) (N D A B : ℕ) (a : Snapshot (aliasArraySize (N+3)))
    (S : Finset ℕ) (n v : ℕ→ℕ) (p : ℕ→Parts)
    (hA:3≤A) (size:a.data.Sized B) (denWidth:D.bits.length≤B)
    (iw:∀k∈OutputPrepare.indexIds,(n k).bits.length≤A)
    (vw:∀k∈OutputRead.ids,(v k).bits.length≤B) (count:n 304=N)
    (targets:∀r∈requests,r.target∈S) (pw:WidthBank S B p)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (state:OutputPoint.State a D v s.val)
    (indexBank:NatAssign.Bank OutputPrepare.indexIds n s.val) (cells:Cells S p s.val) :
    ∃cost t, Executes input tape (code requests) cost s t ∧ cost≤costBound requests A B ∧
      OutputPoint.State a D (readValues a D requests v) t.val ∧
      NatAssign.Bank OutputPrepare.indexIds (indexValues requests n) t.val ∧
      (∀k∈OutputPrepare.indexIds,(indexValues requests n k).bits.length≤ indexWidth requests A) ∧
      (∀k∈OutputRead.ids,(readValues a D requests v k).bits.length≤B) ∧
      indexValues requests n 304=N ∧ Cells S (parts a D requests p) t.val ∧
      WidthBank S B (parts a D requests p) ∧
      t.val.memory=s.val.memory ∧ t.val.inputHead=s.val.inputHead ∧
      t.val.randomCursor=s.val.randomCursor ∧ t.val.output=s.val.output ∧
      (∀k∈OutputPoint.coldIds,t.val.tapes k=s.val.tapes k) ∧
      (∀k,600 ≤ k→(∀r∈requests,k∉cellPorts r.target)→t.val.tapes k=s.val.tapes k) ∧
      (∀k,(k=4 ∨ k=37 ∨ 107 ≤ k)→k<1000→k≠140→(k<530 ∨ 534<k)→t.val.tapes k=s.val.tapes k) := by
  induction requests generalizing A n v p s with
  | nil => exact ⟨1,s,.skip s,le_rfl,state,indexBank,iw,vw,count,cells,pw,rfl,rfl,rfl,rfl,(fun _ _=>rfl),(fun _ _ _=>rfl),fun _ _ _ _ _=>rfl⟩
  | cons r rest ih =>
    obtain ⟨c0,u,e0,b0,state0,index0,iw0,vw0,count0,cells0,pw0,mem0,head0,random0,out0,cold0,high0,middle0⟩:=
      r.executes N D A B a S n v p hA size denWidth iw vw count (targets r (by simp))
        pw input tape s state indexBank cells
    obtain ⟨c1,t,e1,b1,state1,index1,iw1,vw1,count1,cells1,pw1,mem1,head1,random1,out1,cold1,high1,middle1⟩:=
      ih (nextWidth A) _ _ _ (by unfold nextWidth;omega) iw0 vw0 count0
        (fun q hq=>targets q (by simp [hq])) pw0 u state0 index0 cells0
    exact ⟨c0+c1,t,e0.seq e1,Nat.add_le_add b0 b1,state1,index1,iw1,vw1,count1,cells1,pw1,
      mem1.trans mem0,head1.trans head0,random1.trans random0,out1.trans out0,
      (fun k hk=>(cold1 k hk).trans (cold0 k hk)),
      (fun k hk ho=>(high1 k hk (fun q hq=>ho q (by simp [hq]))).trans
        (high0 k hk (ho r (by simp)))),
      fun k lo hi ne outside=>(middle1 k lo hi ne outside).trans (middle0 k lo hi ne outside)⟩

theorem parts_keep {N D : ℕ} (a : Snapshot (aliasArraySize (N+3))) (requests : List Request)
    (p : ℕ→Parts) (i : ℕ) (unused:∀r∈requests,i≠r.target) : parts a D requests p i=p i := by
  induction requests generalizing p with
  | nil => rfl
  | cons r rest ih =>
    rw [parts,ih _ (fun q hq=>unused q (by simp [hq])),Function.update_of_ne (unused r (by simp))]

theorem parts_agree {N D : ℕ} (a : Snapshot (aliasArraySize (N+3))) (requests : List Request)
    (p : ℕ→Parts) (i : ℕ) (x : Parts) (start:p i=x)
    (agree:∀r : Request,r∈requests→ r.target=i→Request.parts r a D=x) : parts a D requests p i=x := by
  induction requests generalizing p with
  | nil => exact start
  | cons r rest ih =>
    apply ih _ ?_ (fun q hq=>agree q (by simp [hq]))
    by_cases eq:i=r.target
    · rw [eq,Function.update_self]
      exact agree r (by simp) eq.symm
    · rw [Function.update_of_ne eq]
      exact start

theorem parts_at {N D : ℕ} (a : Snapshot (aliasArraySize (N+3))) (requests : List Request)
    (p : ℕ→Parts) (r : Request) (member:r∈requests)
    (agree:∀q∈requests,q.target=r.target→ q.parts a D=r.parts a D) :
    parts a D requests p r.target=r.parts a D := by
  induction requests generalizing p with
  | nil => simp at member
  | cons q rest ih =>
    rcases List.mem_cons.mp member with eq|member
    · subst q
      exact parts_agree a rest _ _ _ (Function.update_self _ _ _)
        (fun q hq=>agree q (by simp [hq]))
    · exact ih _ member (fun q hq=>agree q (by simp [hq]))

theorem parts_good {N D : ℕ} (a : Snapshot (aliasArraySize (N+3))) (requests : List Request)
    (S : Finset ℕ) (p : ℕ→Parts) (positive:0<D) (good:Good S p) :
    Good S (parts a D requests p) := by
  induction requests generalizing p with
  | nil => exact good
  | cons r rest ih =>
    apply ih
    intro i hi
    by_cases eq:i=r.target
    · simpa only [eq,Function.update_self,Request.parts,OutputRead.entryParts,Parts.Valid] using positive
    · simpa only [Function.update_of_ne eq] using good i hi

#print axioms executes
end Maxwell.Continuum.Calibration.NeumannMachine.OutputGather
