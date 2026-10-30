import Maxwell.Continuum.CalibrationRootGridFrame
import Maxwell.Continuum.CalibrationRootProductCost

/-! The complete fixed sample program consumes the stored integer index,
decodes its coordinates and phase, and evaluates the literal DFT summand. -/
namespace Maxwell.Continuum.RationalDataflow.RootGrid
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
attribute [local irreducible] sampleCode sampleParts RootProduct.code RootProduct.values

def loadWidth (W : ℕ) : ℕ := 2^8*(W+1)
def sampleWidth (W : ℕ) : ℕ := RootGridCenter.workWidth (loadWidth W)
def sampleCost (N W : ℕ) : ℕ := 2^120*(W+2)^2+
  (2^105+2^145)*(loadWidth W+3)^2+RootProduct.costBound N (sampleWidth W)

theorem sample_executes (S : Finset ℕ) (hS : RootGridCenter.inputs⊆S)
    (N W : ℕ) (n : ℕ→ℕ) (v : ℕ→Parts) (hW : 10≤W) (hN : N.bits.length≤W)
    (hn : ∀i∈ids,(n i).bits.length≤W) (hw : WidthBank S W v) (hg : Good S v)
    (hzero : ∀i∈NaturalQuotient.workPorts,n i=0) (hpos : 0<n 331)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : Ready S v s) (hb : NatAssign.Bank ids n s.val) (hz : ∀i,i<5 → Blank s.val i)
    (hglue : Glue.Clean s.val) (hphase : Phase.Runtime.Clean s.val)
    (hp : Word s.val 640 N) (hq : Word s.val 652 1) (hprec : Word s.val 653 N) :
    ∃cost t,Executes input tape sampleCode cost s t ∧ cost≤sampleCost N W ∧
      Ready S (sampleParts N n v) t ∧ Good S (sampleParts N n v) ∧
      NatAssign.Bank ids (values n) t.val ∧ (∀i,i<5 → Blank t.val i) ∧
      Glue.Clean t.val ∧ Phase.Runtime.Clean t.val ∧
      Word t.val 640 N ∧ Word t.val 652 1 ∧ Word t.val 653 N ∧
      BinaryPrecision.Frame (sampleWorkspace S) s.val t.val := by
  have hU : W≤loadWidth W := by unfold loadWidth;omega
  have hV : W≤sampleWidth W := by unfold sampleWidth RootGridCenter.workWidth;omega
  obtain ⟨c0,s0,e0,h0,b0,z0,f0⟩ := executes n W hzero hpos hn input tape s hb hz
  have r0 := rationalReady_decode hs f0 z0
  have g0 := glueClean_decode hglue f0 z0
  have p0 := phaseClean_decode hphase f0 z0
  have wp0 := word_of_eq (f0.tapes 640 (by decide)) hp
  have wq0 := word_of_eq (f0.tapes 652 (by decide)) hq
  have wn0 := word_of_eq (f0.tapes 653 (by decide)) hprec
  obtain ⟨c1,s1,e1,h1,r1,f1⟩ := load_executes S hS (values n) v (loadWidth W)
    (by omega) (hw.mono hU) (values_width n W hn) input tape s0 r0 b0
  have gw1 : Good S (loadParts (values n) v) := loadParts_good S _ v hg (by
    rw [values_keep n 331 (by decide)];exact hpos)
  have w1 := loadParts_width S (values n) v (loadWidth W) (hw.mono hU) (values_width n W hn)
  have g1 := RootSample.glue_clean_arithmetic g0 f1 r1
  have p1 := Phase.Runtime.Clean.arithmetic_frame p0 f1 r1
  have wp1 := word_of_eq (f1.tapes 640 (FractionWord.outside S 640 (by decide))) wp0
  have wq1 := word_of_eq (f1.tapes 652 (FractionWord.outside S 652 (by decide))) wq0
  have wn1 := word_of_eq (f1.tapes 653 (FractionWord.outside S 653 (by decide))) wn0
  obtain ⟨c2,s2,e2,h2,r2,gw2,w2,f2⟩ := RootGridCenter.executes S hS (loadParts (values n) v)
    (loadWidth W) (by omega) w1 gw1 input tape s1 r1
  have g2 := RootSample.glue_clean_arithmetic g1 f2 r2
  have p2 := Phase.Runtime.Clean.arithmetic_frame p1 f2 r2
  have wp2 := word_of_eq (f2.tapes 640 (FractionWord.outside S 640 (by decide))) wp1
  have wq2 := word_of_eq (f2.tapes 652 (FractionWord.outside S 652 (by decide))) wq1
  have wn2 := word_of_eq (f2.tapes 653 (FractionWord.outside S 653 (by decide))) wn1
  have hSp : RootProduct.inputs⊆S := (show RootProduct.inputs⊆RootGridCenter.inputs by decide).trans hS
  obtain ⟨c3,t,e3,h3,r3,gw3,g3,p3,wp3,wq3,wn3,f3⟩ := RootProduct.executes S hSp N (sampleWidth W)
    (RootGridCenter.values (loadParts (values n) v)) w2 gw2 (hN.trans hV) (hW.trans hV)
    input tape s2 r2 g2 p2 wp2 wq2 wn2
  have fall : BinaryPrecision.Frame (RootProduct.workspace S) s0.val t.val :=
    (f1.mono (rational_subset_product S)).trans ((f2.mono (rational_subset_product S)).trans f3)
  have b3 : NatAssign.Bank ids (values n) t.val := fun i hi =>
    word_of_eq (fall.tapes i (ids_outside_product S i hi)) (b0 i hi)
  have z3 (i : ℕ) (hi : i<5) : Blank t.val i := by
    by_cases hh : i<4
    · exact r3.2 i hh
    have he : i=4 := by omega
    subst i
    exact blank_of_eq (fall.tapes 4 (four_outside_product S)) (z0 4 (by decide))
  refine ⟨c0+(c1+(c2+c3)),t,?_,?_,by simpa only [sampleParts] using r3,
    by simpa only [sampleParts] using gw3,b3,z3,g3,p3,wp3,wq3,wn3,
    (f0.mono Finset.subset_union_left).trans (fall.mono Finset.subset_union_right)⟩
  · simpa only [sampleCode] using e0.seq (e1.seq (e2.seq e3))
  · unfold sampleCost
    nlinarith only [h0,h1,h2,h3]

#print axioms sample_executes
end Maxwell.Continuum.RationalDataflow.RootGrid
