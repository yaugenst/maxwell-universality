import Maxwell.Continuum.RationalDataflowArrayLoop

/-! Runtime traversal for a fixed, verified register-bank program. -/
namespace Maxwell.Continuum.RationalDataflow.PartArray
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

def programIterate {n : ℕ} (a : Table n) (target : ℕ)
    (evaluate : (ℕ→Parts)→(ℕ→Parts)) (v : ℕ→Parts) : ℕ→(ℕ→Parts)
  | 0 => v
  | k+1 => evaluate (Function.update (programIterate a target evaluate v k)
      target (a.getD (n-1-k)))

def programLoaded {n : ℕ} (a : Table n) (target : ℕ)
    (evaluate : (ℕ→Parts)→(ℕ→Parts)) (v : ℕ→Parts) (k : ℕ) : ℕ→Parts :=
  Function.update (programIterate a target evaluate v k) target (a.getD (n-1-k))

def programCode (target : ℕ) (body : Code) : Code :=
  countedProgram 201 (.seq (readCode target) body)

theorem program_executes {n : ℕ} (a : Table n) (S : Finset ℕ) (target : ℕ) (ht : target∈S)
    (body : Code) (evaluate : (ℕ→Parts)→(ℕ→Parts)) (v : ℕ→Parts)
    (B bodyCost : ℕ) (hm : a.MetadataWidth B)
    (hw : ∀ k<n, WidthBank S B (programIterate a target evaluate v k))
    (input : List Bool) (tape : ℕ→Bool)
    (hbody : ∀ k<n, ∀ s : Store,
      RationalDataflow.Ready S (programLoaded a target evaluate v k) s →
      ∃ cost t, Executes input tape body cost s t ∧ cost≤bodyCost ∧
        RationalDataflow.Ready S (evaluate (programLoaded a target evaluate v k)) t ∧
        BinaryPrecision.Frame (workspace S) s.val t.val)
    (xs : List Bool) (origin : ℤ) (hlen : xs.length≤B) (s : Store)
    (hn : addressValue xs=n) (hcount : s.val.tapes 201=BitTape.shifted xs origin)
    (hs : RationalDataflow.Ready S v s) (ha : a.Ready s) :
    ∃ cost t finalWord, Executes input tape (programCode target body) cost s t ∧
      RationalDataflow.Ready S (programIterate a target evaluate v n) t ∧ a.Ready t ∧
      t.val.tapes 201=BitTape.shifted finalWord origin ∧ finalWord.length=xs.length ∧
      cost≤(n+1)*(13*xs.length+15)+n*(2^20*(B+5)^2+bodyCost) := by
  have hout : 201∉workspace S := outside_workspace S 201 (by decide)
  let inv : ℕ→Store→Prop := fun remaining st =>
    remaining≤n ∧ RationalDataflow.Ready S (programIterate a target evaluate v (n-remaining)) st ∧
      a.Ready st
  have stable : ∀ r s t, CountedShifted.Frame 201 s t → inv r s → inv r t := by
    intro r s t f hh
    exact ⟨hh.1,RationalDataflow.Ready.count_frame S _ 201 hout hh.2.1 f,hh.2.2.count_frame f⟩
  have step : ∀ r ys s, inv (r+1) s → s.val.tapes 201=BitTape.shifted ys origin →
      addressValue ys=r → ys.length=xs.length →
      ∃ cost t, Executes input tape (.seq (readCode target) body) cost s t ∧ inv r t ∧
        t.val.tapes 201=BitTape.shifted ys origin ∧ cost≤2^20*(B+5)^2+bodyCost := by
    intro r ys s hh hword hvalue hlength
    have hr : r<n := by have := hh.1; omega
    let k := n-(r+1)
    have hk : k<n := by dsimp [k]; omega
    have hindex : n-1-k=r := by dsimp [k]; omega
    have hget : a.getD (n-1-k)=a.get ⟨r,hr⟩ := by simp only [hindex,Table.getD,dite_eq_left hr]
    obtain ⟨cr,t1,er,hcr,b1,a1,_,f1⟩ := read_executes a S target ht
      (programIterate a target evaluate v k) input tape ys ⟨r,hr⟩ hvalue s hh.2.1 hh.2.2 ⟨origin,hword⟩
    have b1' : RationalDataflow.Ready S (programLoaded a target evaluate v k) t1 := by
      simpa only [programLoaded,hget] using b1
    obtain ⟨ca,t2,ea,hca,b2,f2⟩ := hbody k hk t1 b1'
    have heq : k+1=n-r := by dsimp [k]; omega
    have b2' : RationalDataflow.Ready S (programIterate a target evaluate v (n-r)) t2 := by
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
    omega
  obtain ⟨cost,t,finalWord,he,hh,hword,hl,_,hcost⟩ := counted_executes_sized 201 origin
    (.seq (readCode target) body) input tape xs.length inv (fun _ => 2^20*(B+5)^2+bodyCost)
    stable step n xs s hn hcount rfl ⟨le_rfl,by simpa [inv,programIterate] using hs,ha⟩
  refine ⟨cost,t,finalWord,he,?_,hh.2.2,hword,hl,?_⟩
  · simpa only [Nat.sub_zero] using hh.2.1
  · simpa only [Finset.sum_const,Finset.card_range,smul_eq_mul] using hcost

#print axioms program_executes
end Maxwell.Continuum.RationalDataflow.PartArray
