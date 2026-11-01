import Maxwell.Continuum.CalibrationSeedScalarsMachine
import Maxwell.Continuum.CalibrationSeedRootTerm
import Maxwell.Continuum.RationalDataflowStoredParts

/-! Actual copies of the three computed seed components into the retained
raw bank. Their unreduced channels are used unchanged by the convolution. -/
namespace Maxwell.Continuum.Calibration.SeedRoot
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
set_option maxHeartbeats 2500000
set_option maxRecDepth 12000

def seedSources (j : Fin 3) : Fin 3→ℕ := fun c=>720+3*j.val+c.val
def seedLoadCode : List (Fin 3)→Code
  | [] => .skip
  | j::js => .seq (StoredParts.restoreCode (720+3*j.val) (28+j.val)) (seedLoadCode js)
def seedLoaded : List (Fin 3)→(ℕ→ℕ)→(ℕ→Parts)→ℕ→Parts
  | [],_,v => v
  | j::js,n,v => seedLoaded js n (Function.update v (28+j.val) (SeedMachine.storedComponent n j))

theorem seedSources_small (j c : Fin 3) : seedSources j c<1000 := by
  have hj:=j.isLt
  have hc:=c.isLt
  unfold seedSources
  omega

theorem seedLoad_executes (js : List (Fin 3)) (n : ℕ→ℕ) (v : ℕ→Parts) (B : ℕ)
    (width : WidthBank slots B v) (good : Good slots v)
    (scalarWidth : ∀j,(SeedMachine.storedComponent n j).Width B)
    (scalarGood : ∀j,(SeedMachine.storedComponent n j).Valid)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (ready : Ready slots v s)
    (words : ∀j c,RationalAccumulator.Word s.val (seedSources j c) (n (seedSources j c))) :
    ∃cost t,Executes input tape (seedLoadCode js) cost s t ∧
      cost≤js.length*(63*(B+1))+1 ∧ Ready slots (seedLoaded js n v) t ∧
      WidthBank slots B (seedLoaded js n v) ∧ Good slots (seedLoaded js n v) ∧
      BinaryPrecision.Frame (RationalDataflow.ports slots) s.val t.val := by
  induction js generalizing v s with
  | nil => exact ⟨1,s,.skip s,by simp,ready,width,good,BinaryPrecision.Frame.refl _ _⟩
  | cons j js ih =>
    have hj:=j.isLt
    have member : 28+j.val∈slots := by simp [slots];omega
    have inputs : StoredParts.Stored (720+3*j.val) (SeedMachine.storedComponent n j) s.val := by
      have p:=words j 0
      have q:=words j 1
      have d:=words j 2
      fin_cases j <;> exact ⟨p,q,d⟩
    obtain ⟨c0,u,e0,h0,ru,_,f0⟩ := StoredParts.restore_executes slots (720+3*j.val)
      (28+j.val) (by omega) member v (SeedMachine.storedComponent n j) B (width _ member)
      (scalarWidth j) input tape s ready inputs
    have cells : cellPorts (28+j.val)⊆RationalDataflow.ports slots := by
      intro k hk
      exact Finset.mem_biUnion.mpr ⟨28+j.val,member,hk⟩
    have wu : WidthBank slots B (Function.update v (28+j.val) (SeedMachine.storedComponent n j)) := by
      intro k hk
      by_cases he:k=28+j.val
      · subst k;simpa only [Function.update_self] using scalarWidth j
      · simpa only [Function.update_of_ne he] using width k hk
    have wordsU (k c : Fin 3) : RationalAccumulator.Word u.val (seedSources k c) (n (seedSources k c)) := by
      apply RationalAccumulator.word_of_eq (f0.tapes _ _) (words k c)
      have hs:=seedSources_small k c
      simp only [cellPorts,positivePort,negativePort,denominatorPort,Finset.mem_insert,Finset.mem_singleton]
      omega
    obtain ⟨c1,t,e1,h1,rt,wt,gt,f1⟩ := ih _ wu (good.update _ (scalarGood j)) u ru wordsU
    refine ⟨c0+c1,t,e0.seq e1,?_,rt,wt,gt,(f0.mono cells).trans f1⟩
    simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

theorem seedLoaded_all (n : ℕ→ℕ) (v : ℕ→Parts) (j : Fin 3) :
    seedLoaded [0,1,2] n v (28+j.val)=SeedMachine.storedComponent n j := by
  fin_cases j <;> simp [seedLoaded]

#print axioms seedLoad_executes
end Maxwell.Continuum.Calibration.SeedRoot
