import Maxwell.Continuum.RationalDataflowArrayFrame
import Maxwell.Continuum.RationalDataflowArrayCost
import Maxwell.Continuum.RationalDataflowSizedCounted

/-! One fixed program traverses an input rational array and applies a fixed arithmetic body. -/

namespace Maxwell.Continuum.RationalDataflow.PartArray
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

def Table.getD {n : ℕ} (a : Table n) (i : ℕ) : Parts :=
  if h : i<n then a.get ⟨i,h⟩ else Parts.literal 0

def iterate {n : ℕ} (a : Table n) (target : ℕ) (c : Control) (v : ℕ→Parts) : ℕ→(ℕ→Parts)
  | 0 => v
  | k+1 => c.evaluate (Function.update (iterate a target c v k) target (a.getD (n-1-k)))

def loaded {n : ℕ} (a : Table n) (target : ℕ) (c : Control) (v : ℕ→Parts) (k : ℕ) : ℕ→Parts :=
  Function.update (iterate a target c v k) target (a.getD (n-1-k))

def foldCode (target : ℕ) (c : Control) : Code :=
  countedProgram 201 (.seq (readCode target) c.code)

def foldStepCost (c : Control) (B : ℕ) : ℕ := 2^20*(B+5)^2+c.steps*operationCost B+1

theorem fold_executes {n : ℕ} (a : Table n) (S : Finset ℕ) (target : ℕ) (ht : target∈S)
    (c : Control) (hc : c.Valid S) (v : ℕ→Parts) (B : ℕ) (hm : a.MetadataWidth B)
    (hw : ∀ k<n, WidthBank S B (iterate a target c v k))
    (htrace : ∀ k<n, c.WidthTrace S B (loaded a target c v k))
    (hg : ∀ k<n, Good S (loaded a target c v k))
    (had : ∀ k<n, c.AdmissibleTrace (loaded a target c v k))
    (input : List Bool) (tape : ℕ→Bool) (xs : List Bool) (origin : ℤ)
    (hlen : xs.length≤B) (s : Store) (hn : addressValue xs=n)
    (hcount : s.val.tapes 201=BitTape.shifted xs origin)
    (hs : RationalDataflow.Ready S v s) (ha : a.Ready s) :
    ∃ cost t finalWord, Executes input tape (foldCode target c) cost s t ∧
      RationalDataflow.Ready S (iterate a target c v n) t ∧ a.Ready t ∧
      t.val.tapes 201=BitTape.shifted finalWord origin ∧ finalWord.length=xs.length ∧
      cost≤(n+1)*(13*xs.length+15)+n*foldStepCost c B := by
  have hout : 201∉workspace S := outside_workspace S 201 (by decide)
  let inv : ℕ→Store→Prop := fun remaining st =>
    remaining≤n ∧ RationalDataflow.Ready S (iterate a target c v (n-remaining)) st ∧ a.Ready st
  have stable : ∀ r s t, CountedShifted.Frame 201 s t → inv r s → inv r t := by
    intro r s t f hh
    exact ⟨hh.1,RationalDataflow.Ready.count_frame S _ 201 hout hh.2.1 f,hh.2.2.count_frame f⟩
  have step : ∀ r ys s, inv (r+1) s → s.val.tapes 201=BitTape.shifted ys origin →
      addressValue ys=r → ys.length=xs.length →
      ∃ cost t, Executes input tape (.seq (readCode target) c.code) cost s t ∧ inv r t ∧
        t.val.tapes 201=BitTape.shifted ys origin ∧ cost≤foldStepCost c B := by
    intro r ys s hh hword hvalue hlength
    have hr : r<n := by have := hh.1; omega
    let k := n-(r+1)
    have hk : k<n := by dsimp [k]; omega
    have hindex : n-1-k=r := by dsimp [k]; omega
    have hget : a.getD (n-1-k)=a.get ⟨r,hr⟩ := by simp only [hindex,Table.getD,dite_eq_left hr]
    obtain ⟨cr,t1,er,hcr,b1,a1,_,f1⟩ := read_executes a S target ht
      (iterate a target c v k) input tape ys ⟨r,hr⟩ hvalue s hh.2.1 hh.2.2 ⟨origin,hword⟩
    have b1' : RationalDataflow.Ready S (loaded a target c v k) t1 := by
      simpa only [loaded,hget] using b1
    obtain ⟨ca,t2,ea,hca,b2,f2⟩ := c.executes S hc _ B (htrace k hk) (hg k hk)
      (had k hk) input tape t1 b1'
    have heq : k+1=n-r := by dsimp [k]; omega
    have b2' : RationalDataflow.Ready S (iterate a target c v (n-r)) t2 := by
      rw [← heq]
      exact b2
    have hkeep : 201∉cellPorts target := by
      have hp := positivePort_ge target
      have hn := negativePort_ge target
      have hd := denominatorPort_ge target
      simp only [cellPorts,Finset.mem_insert,Finset.mem_singleton,not_or]
      omega
    refine ⟨cr+ca,t2,er.seq ea,⟨by omega,b2',a1.arithmetic_frame S f2 b2.2⟩,
      (f2.tapes 201 hout).trans ((f1.tapes 201 (by decide) hkeep).trans hword),?_⟩
    have hread := a.readCost_bound B hm ys (by omega) _ (hw k hk target ht)
    unfold foldStepCost
    omega
  obtain ⟨cost,t,finalWord,he,hh,hword,hl,_,hcost⟩ := counted_executes_sized 201 origin
    (.seq (readCode target) c.code) input tape xs.length inv (fun _ => foldStepCost c B)
    stable step n xs s hn hcount rfl ⟨le_rfl,by simpa [inv,iterate] using hs,ha⟩
  refine ⟨cost,t,finalWord,he,?_,hh.2.2,hword,hl,?_⟩
  · simpa only [Nat.sub_zero] using hh.2.1
  · simpa only [Finset.sum_const,Finset.card_range,smul_eq_mul] using hcost

theorem fold_computes {n : ℕ} (a : Table n) (S : Finset ℕ) (target : ℕ) (ht : target∈S)
    (c : Control) (hc : c.Valid S) (v : ℕ→Parts) (B : ℕ) (hm : a.MetadataWidth B)
    (hw : ∀ k<n, WidthBank S B (iterate a target c v k))
    (htrace : ∀ k<n, c.WidthTrace S B (loaded a target c v k))
    (hg : ∀ k<n, Good S (loaded a target c v k))
    (had : ∀ k<n, c.AdmissibleTrace (loaded a target c v k))
    (input : List Bool) (tape : ℕ→Bool) (xs : List Bool) (origin : ℤ)
    (hlen : xs.length≤B) (s : Store) (hn : addressValue xs=n)
    (hcount : s.val.tapes 201=BitTape.shifted xs origin)
    (hs : RationalDataflow.Ready S v s) (ha : a.Ready s) :
    ∃ t,
      (runPriced ((foldCode target c).compile.next input tape)
        ((n+1)*(13*xs.length+15)+n*foldStepCost c B+1) s.val).finished=
          some (t.place (foldCode target c).size) ∧
      RationalDataflow.Ready S (iterate a target c v n) t ∧ a.Ready t := by
  obtain ⟨cost,t,_,he,hb,ha',_,_,hcost⟩ :=
    fold_executes a S target ht c hc v B hm hw htrace hg had input tape xs origin hlen s hn hcount hs ha
  obtain ⟨hrun,_⟩ := he.compiled_run ((n+1)*(13*xs.length+15)+n*foldStepCost c B+1) (by omega)
  exact ⟨t,hrun,hb,ha'⟩

#print axioms fold_computes

end Maxwell.Continuum.RationalDataflow.PartArray
