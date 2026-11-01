import Maxwell.Continuum.CalibrationSeedRootProducer

/-! Six fixed polarization/component producers for each alias row. The
same width bound is restored after every producer, independently of list length. -/
namespace Maxwell.Continuum.Calibration.SeedRoot
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

def phases : List (Fin 3×Fin 2) := [(0,0),(1,0),(2,0),(0,1),(1,1),(2,1)]
def phasesCode : List (Fin 3×Fin 2)→Code
  | [] => .skip
  | p::ps => .seq (producerCode p.1 p.2) (phasesCode ps)
def phasesTable (M D : ℕ) (a : PartArray.Table (2*(2*D+1)^3))
    (row : Fin (ArrayDecodeMachine.aliasRowCount (3*M+D))) (u : Fin 3→ℕ) (v : ℕ→Parts) :
    List (Fin 3×Fin 2)→PartArray.Table (2*aliasArraySize (3*M+D))→PartArray.Table (2*aliasArraySize (3*M+D))
  | [],b => b
  | p::ps,b => phasesTable M D a row u v ps
      (b.set (outputCoordinate M D row p.1 p.2) (entryParts M D a u p.1 p.2 v))

theorem resetNumbers_coordinates (n : ℕ→ℕ) : coordinates (resetNumbers n)=coordinates n := by
  funext k
  fin_cases k <;> simp [coordinates,resetNumbers_keep n 753 (by decide),
    resetNumbers_keep n 754 (by decide),resetNumbers_keep n 755 (by decide)]

theorem phases_executes (M D : ℕ) (a : PartArray.Table (2*(2*D+1)^3))
    (b : PartArray.Table (2*aliasArraySize (3*M+D)))
    (row : Fin (ArrayDecodeMachine.aliasRowCount (3*M+D))) (ps : List (Fin 3×Fin 2))
    (n : ℕ→ℕ) (v : ℕ→Parts) (B : ℕ) (hB : 2≤B)
    (hM : n 750=M) (hD : n 751=D) (half : n 752=n 750/2)
    (hrow : n 780=row.val) (dimension : n 785=aliasArraySize (3*M+D))
    (naturalWidth : ∀i∈rowIds,(n i).bits.length≤B)
    (width : WidthBank slots B (resetParts v)) (good : Good slots (resetParts v))
    (metadata : a.MetadataWidth B) (entryWidth : ∀i,(a.get i).Width B)
    (entryValid : ∀i,(a.get i).Valid) (outputMeta : b.MetadataWidth (producerWidth B))
    (positive : 0<addressValue b.width) (fits : producerWidth B≤addressValue b.width)
    (separated : b.Separated) (disjoint : a.SeparatedFrom b)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (natural : NatAssign.Bank rowIds n s.val) (ready : Ready slots (resetParts v) s)
    (cache : a.Ready s) (output : b.OutputReady s) :
    ∃cost t w,Executes input tape (phasesCode ps) cost s t ∧ cost≤ps.length*producerCost B+1 ∧
      NatAssign.Bank rowIds w t.val ∧ (∀i∈rowIds,(w i).bits.length≤B) ∧
      (∀i∈fixedFields,w i=n i) ∧ Ready slots (resetParts v) t ∧ a.Ready t ∧
      (phasesTable M D a row (coordinates n) v ps b).OutputReady t ∧
      t.val.inputHead=s.val.inputHead ∧ t.val.randomCursor=s.val.randomCursor ∧
      t.val.output=s.val.output ∧ t.val.tapes 4=s.val.tapes 4 ∧
      (∀i,10 ≤ i→i∉producerChanged→t.val.tapes i=s.val.tapes i) ∧
      (∀p∈ps,(entryParts M D a (coordinates n) p.1 p.2 v).Valid ∧
        (entryParts M D a (coordinates n) p.1 p.2 v).Width (producerWidth B)) := by
  induction ps generalizing b n s with
  | nil =>
    exact ⟨1,s,n,Executes.skip s,by simp,natural,naturalWidth,by intro i hi;rfl,
      ready,cache,output,rfl,rfl,rfl,rfl,by intro i hi ho;rfl,by simp⟩
  | cons p ps ih =>
    obtain ⟨c0,u,e0,h0,nu,nwu,ru,au,bu,_,inp0,rnd0,out0,four0,tapes0,valid0,fit0⟩ :=
      producer_executes M D a b row p.1 p.2 n v B hB hM hD half hrow dimension naturalWidth
        width good metadata entryWidth entryValid outputMeta positive fits separated disjoint
        input tape s natural ready cache output
    have hm : resetNumbers n 750=M := (resetNumbers_keep n 750 (by decide)).trans hM
    have hd : resetNumbers n 751=D := (resetNumbers_keep n 751 (by decide)).trans hD
    have hh : resetNumbers n 752=resetNumbers n 750/2 := by
      rw [resetNumbers_keep n 752 (by decide),resetNumbers_keep n 750 (by decide)]
      exact half
    have hr : resetNumbers n 780=row.val := (resetNumbers_keep n 780 (by decide)).trans hrow
    have hn : resetNumbers n 785=aliasArraySize (3*M+D) := (resetNumbers_keep n 785 (by decide)).trans dimension
    obtain ⟨c1,t,w,e1,h1,nt,nwt,keep,rt,ta,tb,inp1,rnd1,out1,four1,tapes1,entries⟩ :=
      ih (b.set (outputCoordinate M D row p.1 p.2) (entryParts M D a (coordinates n) p.1 p.2 v))
        (resetNumbers n) hm hd hh hr hn nwu
        ⟨outputMeta.width,outputMeta.basePositive,outputMeta.baseNegative,outputMeta.baseDenominator,outputMeta.clock⟩
        positive fits separated disjoint u nu ru au bu
    refine ⟨c0+c1,t,w,e0.seq e1,?_,nt,nwt,
      fun i hi=>(keep i hi).trans (resetNumbers_keep n i hi),rt,ta,?_,
      inp1.trans inp0,rnd1.trans rnd0,out1.trans out0,four1.trans four0,
      fun i hi ho=>(tapes1 i hi ho).trans (tapes0 i hi ho),?_⟩
    · have bound := Nat.add_le_add h0 h1
      simpa only [List.length_cons,Nat.add_mul,Nat.one_mul,Nat.add_assoc,Nat.add_left_comm] using bound
    · simpa only [phasesTable,resetNumbers_coordinates] using tb
    · intro q hq
      rcases List.mem_cons.mp hq with rfl|hq
      · exact ⟨valid0,fit0⟩
      · simpa only [resetNumbers_coordinates] using entries q hq

#print axioms phases_executes
end Maxwell.Continuum.Calibration.SeedRoot
