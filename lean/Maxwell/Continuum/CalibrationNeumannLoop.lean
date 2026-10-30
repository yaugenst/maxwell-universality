import Maxwell.Continuum.CalibrationNeumannStep
import Maxwell.Cost.CalibrationMatrix.Horner.Loop

/-! One fixed finite program executes every shared-denominator Neumann layer and reuses its arrays. -/
namespace Maxwell.Continuum.Calibration.NeumannMachine
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.CalibrationMatrix Maxwell.Cost.CalibrationMatrix.Horner
open RationalAccumulator (Blank)
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

theorem Snapshot.Ready.of_memory_tapes {n B : ℕ} {a : Snapshot n} {count : List Bool}
    {s t : BitRAMState} (h : a.Ready count B s) (hm : t.memory=s.memory)
    (keep : ∀ i, i≠140 → t.tapes i=s.tapes i) : a.Ready count B t :=
  ⟨h.1.of_tapes (fun i hi => keep i (by dsimp [WorkTape] at hi; omega)),
    h.2.1.of_memory_tapes hm (fun i hi => keep i (by dsimp [Metadata] at hi; omega)),
    ⟨BankArray.word_of_eq (keep 112 (by omega)) h.2.2.inputPositive,
      BankArray.word_of_eq (keep 113 (by omega)) h.2.2.inputNegative,
      BankArray.word_of_eq (keep 114 (by omega)) h.2.2.outputPositive,
      BankArray.word_of_eq (keep 115 (by omega)) h.2.2.outputNegative⟩⟩

def Invariant {n : ℕ} (a : Snapshot n) (count : List Bool) (N B : ℕ)
    (initial : BitRAMState) (remaining : ℕ) (s : Store) : Prop :=
  remaining≤N ∧ (a.iterate (N-remaining)).Ready count B s.val ∧ Horner.Outside a.data initial s.val

theorem invariant_stable {n : ℕ} (a : Snapshot n) (count : List Bool) (N B : ℕ)
    (initial : BitRAMState) (remaining : ℕ) (s t : Store)
    (hf : CountedShifted.Frame 140 s t) (hs : Invariant a count N B initial remaining s) :
    Invariant a count N B initial remaining t :=
  ⟨hs.1,hs.2.1.of_memory_tapes hf.2.2.1 hf.2.2.2.2.2.1,
    hs.2.2.trans (Horner.Outside.of_memory hf.2.2.1)⟩

def code : Code := .seq (CountedShifted.code 140 stepCode) (.call (TapeOps.clear 140))
def costCap (N n B : ℕ) : ℕ := (N+1)*(13*B+15)+N*stepCost n B+6*B+4

theorem executes {n : ℕ} (a : Snapshot n) (N B : ℕ) (hsized : a.data.Sized B)
    (hm : n*n<2^B) (hn : n<2^B)
    (hfit : ∀ k<N, Fits (a.iterate k).data (a.iterate k).words)
    (input : List Bool) (tape : ℕ→Bool) (count outer : List Bool)
    (hcount : addressValue count=n) (hcl : count.length≤B)
    (houter : addressValue outer=N) (hol : outer.length≤B)
    (origin : ℤ) (s : Store) (hs : a.Ready count B s.val)
    (h140 : s.val.tapes 140=BitTape.shifted outer origin) :
    ∃ cost t, cost≤costCap N n B ∧ Executes input tape code cost s t ∧
      (a.iterate N).Ready count B t.val ∧ Blank t.val 140 ∧ Horner.Outside a.data s.val t.val := by
  let inv := Invariant a count N B s.val
  have stable : ∀ r u v, CountedShifted.Frame 140 u v → inv r u → inv r v :=
    invariant_stable a count N B s.val
  have body : ∀ r xs u, inv (r+1) u →
      u.val.tapes 140=BitTape.shifted xs origin → addressValue xs=r →
      ∃ bodyCost t, Executes input tape stepCode bodyCost u t ∧ inv r t ∧
        t.val.tapes 140=BitTape.shifted xs origin ∧ bodyCost≤stepCost n B := by
    intro r xs u hu hc _
    obtain ⟨hrem,hready,hmem⟩ := hu
    have hk : N-(r+1)<N := by omega
    obtain ⟨cost,t,hcost,he,htr,ht140,htm⟩ := step (a.iterate (N-(r+1))) B
      (a.iterate_sized hsized _) hm hn (hfit _ hk) input tape count hcount hcl u hready
    have hnext : N-r=N-(r+1)+1 := by omega
    refine ⟨cost,t,he,⟨by omega,?_,?_⟩,ht140.trans hc,hcost⟩
    · simpa only [hnext,Snapshot.iterate] using htr
    · exact hmem.trans ((a.iterate_outside (N-(r+1)) u.val t.val).mp htm)
  have initial : inv N s :=
    ⟨le_rfl,by simpa [inv,Snapshot.iterate] using hs,Horner.Outside.refl a.data s.val⟩
  obtain ⟨cost,b,finalCount,he,hbInv,hbCount,hbLen,_,hbCost⟩ :=
    CountedShifted.executes 140 origin stepCode input tape inv (fun _=>stepCost n B)
      stable body N outer s houter h140 initial
  obtain ⟨_,hbr,hbm⟩ := hbInv
  obtain ⟨t,et,ht,ft⟩ := WordCall.clear 140 input tape finalCount origin b hbCount
  have keep (i : ℕ) (hi : i≠140) : t.val.tapes i=b.val.tapes i := by simp [ht,hi]
  refine ⟨cost+(6*finalCount.length+4),t,?_,he.seq et,?_,
    ⟨origin+finalCount.length,by simp [ht]⟩,hbm.trans (Horner.Outside.of_memory ft.2.2.1)⟩
  · simp only [Finset.sum_const,Finset.card_range,smul_eq_mul] at hbCost
    have hlen := hbLen.trans_le hol
    have hcounter : (N+1)*(13*outer.length+15)≤(N+1)*(13*B+15) := by gcongr
    unfold costCap
    omega
  · simpa using hbr.of_memory_tapes ft.2.2.1 keep

theorem compiled_run {n : ℕ} (a : Snapshot n) (N B : ℕ) (hsized : a.data.Sized B)
    (hm : n*n<2^B) (hn : n<2^B)
    (hfit : ∀ k<N, Fits (a.iterate k).data (a.iterate k).words)
    (input : List Bool) (tape : ℕ→Bool) (count outer : List Bool)
    (hcount : addressValue count=n) (hcl : count.length≤B)
    (houter : addressValue outer=N) (hol : outer.length≤B)
    (origin : ℤ) (s : Store) (hs : a.Ready count B s.val)
    (h140 : s.val.tapes 140=BitTape.shifted outer origin) :
    ∃ t : Store,
      (runPriced (code.compile.next input tape) (costCap N n B+1) s.val).finished=some (t.place code.size) ∧
      (runPriced (code.compile.next input tape) (costCap N n B+1) s.val).instructions≤costCap N n B ∧
      (a.iterate N).Ready count B t.val ∧ Blank t.val 140 ∧ Horner.Outside a.data s.val t.val := by
  obtain ⟨cost,t,hc,he,ht⟩ := executes a N B hsized hm hn hfit input tape count outer
    hcount hcl houter hol origin s hs h140
  obtain ⟨hrun,hsteps⟩ := he.compiled_run (costCap N n B+1) (by omega)
  exact ⟨t,hrun,hsteps ▸ hc,ht⟩

theorem costCap_le (N n B : ℕ) : costCap N n B≤3600000*(N+1)*(n+1)^2*(B+2)^2 := by
  have hstep : stepCost n B≤Horner.stepCost n B := by
    unfold stepCost roundCost Horner.stepCost Horner.roundCost
    omega
  have hcost : costCap N n B≤Horner.costCap N n B := by
    unfold costCap Horner.costCap
    gcongr
  exact hcost.trans (Horner.costCap_le N n B)

#print axioms compiled_run
#print axioms costCap_le

end Maxwell.Continuum.Calibration.NeumannMachine
