import Maxwell.Continuum.CalibrationRootGridAccumulate
import Maxwell.Continuum.CalibrationRootGridSources
import Maxwell.Continuum.NaturalBankImportWord

/-! One complete iteration imports the padded runtime counter, evaluates
one sample, and adds it to the two exact rational accumulators. -/
namespace Maxwell.Continuum.RationalDataflow.RootGrid
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
attribute [local irreducible] sampleCode sampleParts RootProduct.code RootProduct.values

def indexedInputs (n : ℕ→ℕ) (index : ℕ) : ℕ→ℕ := Function.update n 330 index
def stepCode : Code := .seq (NaturalImport.code 342 330) (.seq sampleCode accumulate.code)
def stepCost (N W C length : ℕ) : ℕ := 6*W+31*length+39+sampleCost N W+2*operationCost (W+C+1)+1

theorem indexed_width (n : ℕ→ℕ) (index B : ℕ)
    (hn : ∀i∈ids,(n i).bits.length≤B) (hi : index.bits.length≤B) :
    ∀i∈ids,(indexedInputs n index i).bits.length≤B := by
  intro i hm
  by_cases he : i=330
  · subst i
    exact hi
  · simpa only [indexedInputs,Function.update_of_ne he] using hn i hm

theorem indexed_work_zero (n : ℕ→ℕ) (index : ℕ)
    (hz : ∀i∈NaturalQuotient.workPorts,n i=0) :
    ∀i∈NaturalQuotient.workPorts,indexedInputs n index i=0 := by
  intro i hi
  have he : i≠330 := by
    simp only [NaturalQuotient.workPorts,Finset.mem_insert,Finset.mem_singleton] at hi
    omega
  rw [indexedInputs,Function.update_of_ne he,hz i hi]

theorem sample_active_width (N B : ℕ) (n : ℕ→ℕ) (v : ℕ→Parts)
    (hn : ∀i∈ids,(n i).bits.length≤B) (hg : 0<n 331) (hv : (v 9).Width B)
    (i : ℕ) (hi : i<8) : (sampleParts N n v i).Width (coefficientBankWidth N B) := by
  simpa only [sampleParts,coefficientBankWidth] using
    RootProduct.values_active_width N (coefficientInputWidth B)
      (RootGridCenter.values (loadParts (values n) v)) (centered_width n v B hn hg hv)
      (centered_phase_width n v B hn) i hi

theorem step_executes (S : Finset ℕ) (hS : sumInputs⊆S) (N B W : ℕ)
    (n : ℕ→ℕ) (v : ℕ→Parts) (hB : B≤W) (hW : 10≤W) (hN : N.bits.length≤W)
    (hn : ∀i∈ids,(n i).bits.length≤B) (hw : WidthBank S W v) (hg : Good S v)
    (hv : (v 9).Width B) (hC : coefficientBankWidth N B≤W)
    (hzero : ∀i∈NaturalQuotient.workPorts,n i=0) (hpos : 0<n 331)
    (xs : List Bool) (hxW : (addressValue xs).bits.length≤B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : Ready S v s) (hb : NatAssign.Bank ids n s.val) (hz : ∀i,i<5 → Blank s.val i)
    (hglue : Glue.Clean s.val) (hphase : Phase.Runtime.Clean s.val)
    (hp : Word s.val 640 N) (hq : Word s.val 652 1) (hprec : Word s.val 653 N)
    (hword : BankArray.Word s.val 342 xs) :
    ∃cost t,Executes input tape stepCode cost s t ∧
      cost≤stepCost N W (coefficientBankWidth N B) xs.length ∧
      Ready S (accumulated N (indexedInputs n (addressValue xs)) v) t ∧
      Good S (accumulated N (indexedInputs n (addressValue xs)) v) ∧
      WidthBank S (W+coefficientBankWidth N B+1) (accumulated N (indexedInputs n (addressValue xs)) v) ∧
      NatAssign.Bank ids (values (indexedInputs n (addressValue xs))) t.val ∧
      (∀i,i<5 → Blank t.val i) ∧ Glue.Clean t.val ∧ Phase.Runtime.Clean t.val ∧
      Word t.val 640 N ∧ Word t.val 652 1 ∧ Word t.val 653 N ∧
      BinaryPrecision.Frame (sampleWorkspace S) s.val t.val := by
  obtain ⟨c0,s0,e0,h0,b0,f0⟩ := NaturalImport.executes ids 342 330 (by decide) (by decide)
    n xs input tape s hb hword
  have fd : BinaryPrecision.Frame decodeWorkspace s.val s0.val := f0.mono (by decide)
  have z0 (i : ℕ) (hi : i<5) : Blank s0.val i :=
    blank_of_eq (f0.tapes i (by simp only [Finset.mem_singleton];omega)) (hz i hi)
  have r0 := rationalReady_decode hs fd z0
  have g0 := glueClean_decode hglue fd z0
  have p0 := phaseClean_decode hphase fd z0
  have wp0 := word_of_eq (f0.tapes 640 (by decide)) hp
  have wq0 := word_of_eq (f0.tapes 652 (by decide)) hq
  have wn0 := word_of_eq (f0.tapes 653 (by decide)) hprec
  have niw := indexed_width n (addressValue xs) B hn hxW
  have nip : 0 < indexedInputs n (addressValue xs) 331 := by
    simpa only [indexedInputs,Function.update_of_ne (by decide : (331:ℕ)≠330)] using hpos
  have hSc : RootGridCenter.inputs⊆S := Finset.subset_union_left.trans hS
  obtain ⟨c1,s1,e1,h1,r1,g1,b1,z1,gl1,ph1,wp1,wq1,wn1,f1⟩ := sample_executes S hSc N W
    (indexedInputs n (addressValue xs)) v hW hN (fun i hi => (niw i hi).trans hB) hw hg
    (indexed_work_zero n _ hzero) nip input tape s0 r0 b0 z0 g0 p0 wp0 wq0 wn0
  have w1 : WidthBank S W (sampleParts N (indexedInputs n (addressValue xs)) v) := by
    simpa only [Nat.max_eq_left hC] using sampleParts_width S N B W
      (indexedInputs n (addressValue xs)) v niw nip hv hw
  have w6 := sample_active_width N B (indexedInputs n (addressValue xs)) v niw nip hv 6 (by decide)
  have w7 := sample_active_width N B (indexedInputs n (addressValue xs)) v niw nip hv 7 (by decide)
  obtain ⟨c2,t,e2,h2,r2,g2,w2,f2⟩ := accumulate_executes S hS _ W (coefficientBankWidth N B)
    w1 w6 w7 g1 input tape s1 r1
  have b2 : NatAssign.Bank ids (values (indexedInputs n (addressValue xs))) t.val := fun i hi =>
    word_of_eq (f2.tapes i (ids_outside_rational S i hi)) (b1 i hi)
  have z2 (i : ℕ) (hi : i<5) : Blank t.val i := by
    by_cases he : i<4
    · exact r2.2 i he
    have hi4 : i=4 := by omega
    subst i
    exact blank_of_eq ((f2.mono (rational_subset_product S)).tapes 4 (four_outside_product S)) (z1 4 (by decide))
  have gl2 := RootSample.glue_clean_arithmetic gl1 f2 r2
  have ph2 := Phase.Runtime.Clean.arithmetic_frame ph1 f2 r2
  have wp2 := word_of_eq (f2.tapes 640 (FractionWord.outside S 640 (by decide))) wp1
  have wq2 := word_of_eq (f2.tapes 652 (FractionWord.outside S 652 (by decide))) wq1
  have wn2 := word_of_eq (f2.tapes 653 (FractionWord.outside S 653 (by decide))) wn1
  refine ⟨c0+(c1+c2),t,e0.seq (e1.seq e2),?_,r2,g2,w2,b2,z2,gl2,ph2,wp2,wq2,wn2,
    (fd.mono Finset.subset_union_left).trans (f1.trans (f2.mono ?_))⟩
  · have hn330 := (hn 330 (by decide)).trans hB
    unfold stepCost
    omega
  · exact (rational_subset_product S).trans Finset.subset_union_right

#print axioms step_executes
end Maxwell.Continuum.RationalDataflow.RootGrid
