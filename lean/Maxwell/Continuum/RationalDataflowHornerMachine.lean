import Maxwell.Continuum.RationalDataflowArrayHorner

/-! The fixed Horner code, including accumulator initialization and all indexed reads. -/
namespace Maxwell.Continuum.RationalDataflow.PartArray
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

def hornerCode : Code :=
  .seq (NatAssign.code (literalStage 0 (Parts.literal 0))) (foldCode 1 hornerBody)

def hornerCost (n W wordLength : ℕ) : ℕ :=
  stageCost (hornerWidth n W)+(n+1)*(13*wordLength+15)+
    n*(2^20*(hornerWidth n W+5)^2+2*operationCost (hornerWidth n W)+1)

theorem horner_executes {n : ℕ} (a : Table n) (S : Finset ℕ)
    (h0 : 0∈S) (h1 : 1∈S) (h2 : 2∈S)
    (W : ℕ) (hW : 1≤W) (hmeta : a.MetadataWidth W)
    (haWidth : ∀ i, (a.get i).Width W) (haValid : ∀ i, (a.get i).Valid)
    (v : ℕ→Parts) (hv : WidthBank S W v) (hgood : Good S v)
    (input : List Bool) (tape : ℕ→Bool) (xs : List Bool) (origin : ℤ)
    (hlen : xs.length≤W) (s : Store) (hn : addressValue xs=n)
    (hcount : s.val.tapes 201=BitTape.shifted xs origin)
    (hs : RationalDataflow.Ready S v s) (ha : a.Ready s) :
    ∃ cost t output finalWord, Executes input tape hornerCode cost s t ∧
      cost≤hornerCost n W xs.length ∧ RationalDataflow.Ready S output t ∧ a.Ready t ∧
      t.val.tapes 201=BitTape.shifted finalWord origin ∧ finalWord.length=xs.length ∧
      Good S output ∧ WidthBank S (hornerWidth n W) output ∧
      output 0=reverseHorner a (v 2) n ∧
      (∀ i, i≠0 → i≠1 → output i=v i) ∧
      output=iterate a 1 hornerBody (sumStart v 0) n := by
  have hB : W≤hornerWidth n W := by unfold hornerWidth; nlinarith
  have hzero : (Parts.literal (0:ℚ)).Width (hornerWidth n W) :=
    (Parts.literal_width RationalWords.width_zero').mono (hW.trans hB)
  obtain ⟨c0,t0,e0,hc0,b0,f0⟩ := literal_executes S 0 h0 (Parts.literal 0) v
    (hornerWidth n W) hzero (hv.mono hB) input tape s hs
  have a0 := ha.arithmetic_frame S f0 b0.2
  have outside : 201∉workspace S := outside_workspace S 201 (by decide)
  have before (k : ℕ) (hk : k<n) : WidthBank S (hornerWidth n W)
      (iterate a 1 hornerBody (sumStart v 0) k) := by
    apply (horner_iterate_width a S h0 h2 W hW haWidth v hv k).mono
    unfold hornerWidth
    exact Nat.add_le_add_right (Nat.mul_le_mul_right _ (by omega)) 1
  have good (k : ℕ) (_hk : k<n) : Good S (loaded a 1 hornerBody (sumStart v 0) k) :=
    (horner_iterate_good a S h0 h1 h2 haValid v hgood k).update 1 (a.getD_valid haValid _)
  obtain ⟨c1,t,finalWord,e1,b1,a1,count1,length1,hc1⟩ := fold_executes a S 1 h1
    hornerBody ⟨⟨h0,h0,h2⟩,⟨h0,h0,h1⟩,trivial⟩ (sumStart v 0)
    (hornerWidth n W) (hmeta.mono hB) before
    (horner_widthTrace a S h0 h2 W hW haWidth v hv) good
    (fun _ _ => ⟨trivial,trivial,trivial⟩) input tape xs origin (hlen.trans hB) t0 hn
    ((f0.tapes 201 outside).trans hcount) b0 a0
  refine ⟨c0+c1,t,iterate a 1 hornerBody (sumStart v 0) n,finalWord,e0.seq e1,?_,
    b1,a1,count1,length1,horner_iterate_good a S h0 h1 h2 haValid v hgood n,
    horner_iterate_width a S h0 h2 W hW haWidth v hv n,
    horner_iterate_accumulator a v n,horner_iterate_keep a v n,rfl⟩
  simp only [foldStepCost,hornerBody,Control.steps,Nat.add_zero,Nat.reduceAdd] at hc1
  unfold hornerCost
  omega

theorem hornerCost_polynomial (n W wordLength : ℕ) :
    hornerCost n W wordLength≤2^112*(n+1)^3*(W+2)^2+(n+1)*(13*wordLength+15) := by
  have hw : hornerWidth n W+5≤8*(n+1)*(W+2) := by unfold hornerWidth; nlinarith
  have hw2 : hornerWidth n W+2≤8*(n+1)*(W+2) := by omega
  have hw3 : hornerWidth n W+3≤8*(n+1)*(W+2) := by omega
  have hs := Nat.pow_le_pow_left hw2 2
  have ho := Nat.pow_le_pow_left hw3 2
  have hr := Nat.pow_le_pow_left hw 2
  have hpos : 1≤(n+1)^2*(W+2)^2 := Nat.succ_le_of_lt (by positivity)
  have hstage : stageCost (hornerWidth n W)≤2^103*(n+1)^2*(W+2)^2 := by
    unfold stageCost
    nlinarith only [hs]
  have hbody : 2^20*(hornerWidth n W+5)^2+2*operationCost (hornerWidth n W)+1≤
      2^109*(n+1)^2*(W+2)^2 := by
    unfold operationCost
    nlinarith only [ho,hr,hpos]
  have hm := Nat.mul_le_mul_left n hbody
  unfold hornerCost
  nlinarith only [hstage,hm,Nat.zero_le ((n+1)^2*(W+2)^2)]

theorem horner_computes {n : ℕ} (a : Table n) (S : Finset ℕ)
    (h0 : 0∈S) (h1 : 1∈S) (h2 : 2∈S)
    (W : ℕ) (hW : 1≤W) (hmeta : a.MetadataWidth W)
    (haWidth : ∀ i, (a.get i).Width W) (haValid : ∀ i, (a.get i).Valid)
    (v : ℕ→Parts) (hv : WidthBank S W v) (hgood : Good S v)
    (input : List Bool) (tape : ℕ→Bool) (xs : List Bool) (origin : ℤ)
    (hlen : xs.length≤W) (s : Store) (hn : addressValue xs=n)
    (hcount : s.val.tapes 201=BitTape.shifted xs origin)
    (hs : RationalDataflow.Ready S v s) (ha : a.Ready s) :
    ∃ t output,
      (runPriced (hornerCode.compile.next input tape) (hornerCost n W xs.length+1) s.val).finished=
        some (t.place hornerCode.size) ∧
      (runPriced (hornerCode.compile.next input tape) (hornerCost n W xs.length+1) s.val).instructions≤
        2^112*(n+1)^3*(W+2)^2+(n+1)*(13*xs.length+15) ∧
      RationalDataflow.Ready S output t ∧ a.Ready t ∧
      (output 0).value=∑ i : Fin n, (a.get i).value*(v 2).value^i.val := by
  obtain ⟨cost,t,output,_,he,hcost,hbank,harray,_,_,_,_,hresult,_,_⟩ :=
    horner_executes a S h0 h1 h2 W hW hmeta haWidth haValid v hv hgood
      input tape xs origin hlen s hn hcount hs ha
  obtain ⟨hrun,hsteps⟩ := he.compiled_run (hornerCost n W xs.length+1) (by omega)
  refine ⟨t,output,hrun,hsteps ▸ hcost.trans (hornerCost_polynomial n W xs.length),hbank,harray,?_⟩
  rw [hresult,reverseHorner_value a (v 2) haValid (hgood 2 h2)]

#print axioms horner_computes
#print axioms hornerCost_polynomial
end Maxwell.Continuum.RationalDataflow.PartArray
