import Maxwell.Continuum.CalibrationRootFrequencyFrame

/-! One fixed runtime decoder saves parity in shared register eight and
computes the three literal modular negative frequencies. -/
namespace Maxwell.Continuum.RationalDataflow.RootFrequency
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 3500000
set_option maxRecDepth 8192

def code : Code := .seq headCode (.seq (FractionWord.code 341 344 8) tailCode)
def workspace (S : Finset ℕ) : Finset ℕ := changed∪RationalDataflow.workspace S
def parityParts (n : ℕ→ℕ) (v : ℕ→Parts) := Function.update v 8 (FractionWord.part (n 330%2) 1)
def costBound (B I : ℕ) : ℕ :=
  2^107*(B+2)^2+2^103*(B+I+5)^2+2^130*(4*(B+1)+2)^2

theorem parity_valid (index : ℕ) : (FractionWord.part (index%2) 1).Valid := by
  change 0<(1:ℕ)
  decide

theorem parity_width (index : ℕ) : (FractionWord.part (index%2) 1).Width 1 := by
  have hi := Nat.mod_lt index (by decide : 0<2)
  have hb : (index%2).bits.length≤1 := (RationalWords.bits_mono (show index%2≤1 by omega)).trans
    (show (1:ℕ).bits.length≤1 by decide)
  exact ⟨hb,by change (0:ℕ).bits.length≤1;decide,by change (1:ℕ).bits.length≤1;decide⟩

theorem parity_value (index : ℕ) : (FractionWord.part (index%2) 1).value=(index%2:ℕ) := by
  simp [FractionWord.part,Parts.value]

theorem code_executes (S : Finset ℕ) (h8 : 8∈S) (n : ℕ→ℕ) (v : ℕ→Parts)
    (N B I : ℕ) (hB : 2≤B) (hI : 1≤I)
    (hn : ∀i∈ids,(n i).bits.length≤B) (hw : WidthBank S I v) (hg : Good S v)
    (hz : ∀i∈NaturalQuotient.workPorts,n i=0) (hp : 0 < n 331)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hb : NatAssign.Bank ids n s.val) (hr : Ready S v s)
    (hblank : ∀i,i<5 → Blank s.val i)
    (hglue : Glue.Clean s.val) (hphase : Phase.Runtime.Clean s.val)
    (hprec : Word s.val 640 N) (hQ : Word s.val 652 1) (hprec' : Word s.val 653 N) :
    ∃cost t,Executes input tape code cost s t ∧ cost≤costBound B I ∧
      NatAssign.Bank ids (values n) t.val ∧ Ready S (parityParts n v) t ∧
      Good S (parityParts n v) ∧ WidthBank S I (parityParts n v) ∧
      (∀i,i<5 → Blank t.val i) ∧ Glue.Clean t.val ∧ Phase.Runtime.Clean t.val ∧
      Word t.val 640 N ∧ Word t.val 652 1 ∧ Word t.val 653 N ∧
      BinaryPrecision.Frame (workspace S) s.val t.val := by
  obtain ⟨c0,s0,e0,h0,b0,z0,f0⟩ := head_executes n B hB hn hz input tape s hb hblank
  have r0 := rational_frame hr f0 z0
  have g0 := glue_frame hglue f0 z0
  have p0 := phase_frame hphase f0 z0
  have p640 := word_of_eq (f0.tapes 640 (by decide)) hprec
  have p652 := word_of_eq (f0.tapes 652 (by decide)) hQ
  have p653 := word_of_eq (f0.tapes 653 (by decide)) hprec'
  have wa : Word s0.val 341 (n 330%2) := by
    simpa only [(pair_values n).2.1] using b0 341 (by decide)
  have wb : Word s0.val 344 1 := by
    simpa only [(pair_values n).2.2.2.2] using b0 344 (by decide)
  have hmod : (n 330%2).bits.length≤B+I+2 :=
    (RationalWords.bits_mono (Nat.mod_le _ _)).trans ((hn 330 (by decide)).trans (by omega))
  obtain ⟨c1,s1,e1,h1,r1,f1⟩ := FractionWord.executes S 341 344 8 (by decide) (by decide) h8
    (n 330%2) 1 (B+I+2) v (hw.mono (by omega)) (by omega) hmod
    (by change 1≤B+I+2;omega) input tape s0 r0 wa wb
  have b1 : NatAssign.Bank ids (pair n) s1.val := fun i hi =>
    word_of_eq (f1.tapes i (ids_outside_rational S i hi)) (b0 i hi)
  have z1 (i : ℕ) (hi : i<5) : Blank s1.val i := by
    by_cases h4 : i<4
    · exact r1.2 i h4
    have he : i=4 := by omega
    subst i
    exact blank_of_eq (f1.tapes 4 (by
      have hh := RootGrid.four_outside_product S
      exact fun hm => hh (RootGrid.rational_subset_product S hm))) (z0 4 (by decide))
  have g1 := RootSample.glue_clean_arithmetic g0 f1 r1
  have p1 := Phase.Runtime.Clean.arithmetic_frame p0 f1 r1
  have q640 := word_of_eq (f1.tapes 640 (FractionWord.outside S 640 (by decide))) p640
  have q652 := word_of_eq (f1.tapes 652 (FractionWord.outside S 652 (by decide))) p652
  have q653 := word_of_eq (f1.tapes 653 (FractionWord.outside S 653 (by decide))) p653
  have hn0 : ∀i∈ids,(pair n i).bits.length≤4*(B+1) := by
    have ww := Calibration.ArrayDecodeMachine.nat_values_width ids prepare prepare_valid n B hn
      (by simp [prepare,NatAssign.Instruction.literalWidth,show (2:ℕ).bits.length=2 by rfl];omega)
    have w0 : ∀i∈ids,(prepared n i).bits.length≤4*(B+1) := by
      simpa only [prepared,show prepare.length=2 by rfl,show 2^2=4 by rfl] using ww
    exact Calibration.ArrayDecodeMachine.divModValues_width (prepared n) ids 330 343 330 341 _ (by decide) w0
  obtain ⟨c2,t,e2,h2,b2,z2,f2⟩ := tail_executes n (4*(B+1)) hn0 hz hp input tape s1 b1 z1
  have good : Good S (parityParts n v) := by
    intro i hi
    by_cases he : i=8
    · subst i
      exact parity_valid (n 330)
    · simpa only [parityParts,Function.update_of_ne he] using hg i hi
  have width : WidthBank S I (parityParts n v) := hw.update 8 ((parity_width (n 330)).mono hI)
  have h1' : c1≤2^103*(B+I+5)^2 := by simpa only [Nat.add_assoc] using h1
  refine ⟨c0+(c1+c2),t,e0.seq (e1.seq e2),by unfold costBound;omega,b2,
    rational_frame r1 f2 z2,good,width,z2,glue_frame g1 f2 z2,phase_frame p1 f2 z2,
    word_of_eq (f2.tapes 640 (by decide)) q640,
    word_of_eq (f2.tapes 652 (by decide)) q652,
    word_of_eq (f2.tapes 653 (by decide)) q653,
    (f0.mono Finset.subset_union_left).trans
      ((f1.mono Finset.subset_union_right).trans (f2.mono Finset.subset_union_left))⟩

#print axioms code_executes
end Maxwell.Continuum.RationalDataflow.RootFrequency
