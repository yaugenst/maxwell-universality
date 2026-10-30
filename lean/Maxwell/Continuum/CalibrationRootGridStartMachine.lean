import Maxwell.Continuum.CalibrationRootGridStart

/-! Charged startup preserves the complete elementary-call state while
creating the countdown and denominator words from the stored grid size. -/
namespace Maxwell.Continuum.RationalDataflow.RootGrid
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 3500000
set_option maxRecDepth 8192

theorem start_executes (S : Finset ℕ) (hS : sumInputs⊆S) (N B I : ℕ)
    (n : ℕ→ℕ) (v : ℕ→Parts) (hB : 1≤B) (hI : 1≤I)
    (hn : ∀i∈clockIds,(n i).bits.length≤B) (hw : WidthBank S I v) (hg : Good S v)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : Ready S v s) (hb : NatAssign.Bank ids n s.val) (hc : NatAssign.Bank clockIds n s.val)
    (hz : ∀i,i<5 → Blank s.val i) (hglue : Glue.Clean s.val) (hphase : Phase.Runtime.Clean s.val)
    (hp : Word s.val 640 N) (hq : Word s.val 652 1) (hprec : Word s.val 653 N) :
    ∃cost t,Executes input tape startCode cost s t ∧ cost≤stageCost B+2*operationCost I+1 ∧
      Ready S (zeroValues v) t ∧ Good S (zeroValues v) ∧ WidthBank S I (zeroValues v) ∧
      NatAssign.Bank ids n t.val ∧ NatAssign.Bank clockIds (clockValues n) t.val ∧
      (∀i,i<5 → Blank t.val i) ∧ Glue.Clean t.val ∧ Phase.Runtime.Clean t.val ∧
      Word t.val 640 N ∧ Word t.val 652 1 ∧ Word t.val 653 N ∧
      BinaryPrecision.Frame (startWorkspace S) s.val t.val := by
  obtain ⟨c0,s0,e0,h0,b0,z0,f0⟩ := clock_executes n B hB hn input tape s hc (fun i hi => hz i (by omega))
  have r0 := rationalReady_clock hs f0 z0
  have g0 := glueClean_clock hglue f0
  have p0 := phaseClean_clock hphase f0
  have wp0 := word_of_eq (f0.tapes 640 (by decide)) hp
  have wq0 := word_of_eq (f0.tapes 652 (by decide)) hq
  have wn0 := word_of_eq (f0.tapes 653 (by decide)) hprec
  have bnat0 : NatAssign.Bank ids n s0.val := by
    intro i hi
    by_cases he : i=331
    · subst i
      simpa only [(clockValues_result n).1] using b0 331 (by decide)
    · have hout : i∉clockWorkspace := by
        have bound := ids_bounds i hi
        simp only [clockWorkspace,clockIds,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
        omega
      exact word_of_eq (f0.tapes i hout) (hb i hi)
  have hz04 : Blank s0.val 4 := blank_of_eq (f0.tapes 4 (by decide)) (hz 4 (by decide))
  have ht := zeroSums_widthTrace S v I hI hw
  obtain ⟨c1,t,e1,h1,r1,f1⟩ := zeroSums.executes S (zeroSums_valid S hS) v I ht hg
    (zeroSums_admissible v) input tape s0 r0
  have bnat1 : NatAssign.Bank ids n t.val := fun i hi =>
    word_of_eq (f1.tapes i (ids_outside_rational S i hi)) (bnat0 i hi)
  have bclock1 : NatAssign.Bank clockIds (clockValues n) t.val := fun i hi =>
    word_of_eq (f1.tapes i (clock_outside_rational S i hi)) (b0 i hi)
  have z1 (i : ℕ) (hi : i<5) : Blank t.val i := by
    by_cases he : i<4
    · exact r1.2 i he
    have hi4 : i=4 := by omega
    subst i
    exact blank_of_eq ((f1.mono (rational_subset_product S)).tapes 4 (four_outside_product S)) hz04
  refine ⟨c0+c1,t,e0.seq e1,?_,r1,zeroSums.evaluate_good S (zeroSums_valid S hS) v hg
    (zeroSums_admissible v),ht.result,bnat1,bclock1,z1,
    RootSample.glue_clean_arithmetic g0 f1 r1,Phase.Runtime.Clean.arithmetic_frame p0 f1 r1,
    word_of_eq (f1.tapes 640 (FractionWord.outside S 640 (by decide))) wp0,
    word_of_eq (f1.tapes 652 (FractionWord.outside S 652 (by decide))) wq0,
    word_of_eq (f1.tapes 653 (FractionWord.outside S 653 (by decide))) wn0,
    (f0.mono Finset.subset_union_left).trans (f1.mono Finset.subset_union_right)⟩
  change c1≤2*operationCost I+1 at h1
  omega

#print axioms start_executes
end Maxwell.Continuum.RationalDataflow.RootGrid
