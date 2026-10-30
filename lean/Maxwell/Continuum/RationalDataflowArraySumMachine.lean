import Maxwell.Continuum.RationalDataflowArraySum

/-! End-to-end bit-machine execution of a finite rational sum, including accumulator initialization. -/

namespace Maxwell.Continuum.RationalDataflow.PartArray
open Maxwell.Cost Maxwell.Cost.Structured
open scoped BigOperators
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

def sumCode (accumulator entry : ℕ) : Code :=
  .seq (NatAssign.code (literalStage accumulator (Parts.literal 0)))
    (foldCode entry (sumBody accumulator entry))

def sumCost (n W wordLength : ℕ) : ℕ :=
  stageCost (sumWidth n W)+(n+1)*(13*wordLength+15)+
    n*(2^20*(sumWidth n W+5)^2+operationCost (sumWidth n W)+1)

theorem sum_executes {n : ℕ} (a : Table n) (S : Finset ℕ) (accumulator entry : ℕ)
    (hacc : accumulator∈S) (hentry : entry∈S) (hne : accumulator≠entry)
    (W : ℕ) (hW : 1≤W) (hmeta : a.MetadataWidth W)
    (haWidth : ∀ i, (a.get i).Width W) (haValid : ∀ i, (a.get i).Valid)
    (v : ℕ→Parts) (hv : WidthBank S W v) (hgood : Good S v)
    (input : List Bool) (tape : ℕ→Bool) (xs : List Bool) (origin : ℤ)
    (hlen : xs.length≤W) (s : Store) (hn : addressValue xs=n)
    (hcount : s.val.tapes 201=BitTape.shifted xs origin)
    (hs : RationalDataflow.Ready S v s) (ha : a.Ready s) :
    ∃ cost t output, Executes input tape (sumCode accumulator entry) cost s t ∧
      cost≤sumCost n W xs.length ∧ RationalDataflow.Ready S output t ∧ a.Ready t ∧
      (output accumulator).value=∑ i : Fin n, (a.get i).value := by
  have hB : W≤sumWidth n W := by unfold sumWidth; nlinarith
  have hzero : (Parts.literal (0:ℚ)).Width (sumWidth n W) :=
    (Parts.literal_width RationalWords.width_zero').mono (hW.trans hB)
  obtain ⟨c0,t0,e0,h0,b0,f0⟩ := literal_executes S accumulator hacc (Parts.literal 0) v
    (sumWidth n W) hzero (hv.mono hB) input tape s hs
  have t0a := ha.arithmetic_frame S f0 b0.2
  have hout : 201∉workspace S := outside_workspace S 201 (by decide)
  have before (k : ℕ) (hk : k<n) : WidthBank S (sumWidth n W)
      (iterate a entry (sumBody accumulator entry) (sumStart v accumulator) k) := by
    apply (sum_iterate_width a S accumulator entry hne W hW haWidth v hv hacc k).mono
    unfold sumWidth
    exact Nat.add_le_add_right (Nat.mul_le_mul_right (W+1) (by omega)) 1
  have good (k : ℕ) (_hk : k<n) :
      Good S (loaded a entry (sumBody accumulator entry) (sumStart v accumulator) k) :=
    (sum_iterate_good a S accumulator entry haValid v hgood hacc hentry k).update entry
      (a.getD_valid haValid _)
  obtain ⟨c1,t,_,e1,b1,a1,_,_,h1⟩ := fold_executes a S entry hentry
    (sumBody accumulator entry) ⟨⟨hacc,hacc,hentry⟩,trivial⟩ (sumStart v accumulator)
    (sumWidth n W) (hmeta.mono hB) before
    (sum_widthTrace a S accumulator entry hne W hW haWidth v hv hacc) good
    (fun _ _ => ⟨trivial,trivial⟩) input tape xs origin (hlen.trans hB) t0 hn
    ((f0.tapes 201 hout).trans hcount) b0 t0a
  refine ⟨c0+c1,t,iterate a entry (sumBody accumulator entry) (sumStart v accumulator) n,
    e0.seq e1,?_,b1,a1,sum_iterate_value a accumulator entry hne haValid v⟩
  simp only [foldStepCost,sumBody,Control.steps,Nat.add_zero,Nat.one_mul] at h1
  unfold sumCost
  omega

theorem sum_computes {n : ℕ} (a : Table n) (S : Finset ℕ) (accumulator entry : ℕ)
    (hacc : accumulator∈S) (hentry : entry∈S) (hne : accumulator≠entry)
    (W : ℕ) (hW : 1≤W) (hmeta : a.MetadataWidth W)
    (haWidth : ∀ i, (a.get i).Width W) (haValid : ∀ i, (a.get i).Valid)
    (v : ℕ→Parts) (hv : WidthBank S W v) (hgood : Good S v)
    (input : List Bool) (tape : ℕ→Bool) (xs : List Bool) (origin : ℤ)
    (hlen : xs.length≤W) (s : Store) (hn : addressValue xs=n)
    (hcount : s.val.tapes 201=BitTape.shifted xs origin)
    (hs : RationalDataflow.Ready S v s) (ha : a.Ready s) :
    ∃ t output,
      (runPriced ((sumCode accumulator entry).compile.next input tape)
        (sumCost n W xs.length+1) s.val).finished=some (t.place (sumCode accumulator entry).size) ∧
      (runPriced ((sumCode accumulator entry).compile.next input tape)
        (sumCost n W xs.length+1) s.val).instructions≤sumCost n W xs.length ∧
      RationalDataflow.Ready S output t ∧ a.Ready t ∧
      (output accumulator).value=∑ i : Fin n, (a.get i).value := by
  obtain ⟨cost,t,output,he,hcost,hb,ha',hv'⟩ := sum_executes a S accumulator entry hacc hentry hne
    W hW hmeta haWidth haValid v hv hgood input tape xs origin hlen s hn hcount hs ha
  obtain ⟨hrun,hsteps⟩ := he.compiled_run (sumCost n W xs.length+1) (by omega)
  exact ⟨t,output,hrun,hsteps ▸ hcost,hb,ha',hv'⟩

theorem sumCost_polynomial (n W wordLength : ℕ) :
    sumCost n W wordLength≤2^110*(n+1)^3*(W+2)^2+(n+1)*(13*wordLength+15) := by
  have hw : sumWidth n W+5≤7*(n+1)*(W+2) := by unfold sumWidth; nlinarith
  have hw2 : sumWidth n W+2≤7*(n+1)*(W+2) := by omega
  have hw3 : sumWidth n W+3≤7*(n+1)*(W+2) := by omega
  have hs := Nat.pow_le_pow_left hw2 2
  have ho := Nat.pow_le_pow_left hw3 2
  have hr := Nat.pow_le_pow_left hw 2
  have hpos : 1≤(n+1)^2*(W+2)^2 := Nat.succ_le_of_lt (by positivity)
  have hstage : stageCost (sumWidth n W)≤2^103*(n+1)^2*(W+2)^2 := by
    unfold stageCost
    nlinarith only [hs]
  have hbody : 2^20*(sumWidth n W+5)^2+operationCost (sumWidth n W)+1≤
      2^107*(n+1)^2*(W+2)^2 := by
    unfold operationCost
    nlinarith only [ho,hr,hpos]
  have hm := Nat.mul_le_mul_left n hbody
  unfold sumCost
  nlinarith only [hstage,hm,Nat.zero_le ((n+1)^2*(W+2)^2)]

#print axioms sum_computes
#print axioms sumCost_polynomial

end Maxwell.Continuum.RationalDataflow.PartArray
