import Maxwell.Continuum.CalibrationRootFrequencyMachine

/-! An actual flat runtime index drives the literal Fourier coefficient
evaluation; the inner countdown is cleared before returning. -/
namespace Maxwell.Continuum.RationalDataflow.RootIndexed
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

def decodedWidth (B : ℕ) : ℕ := 32768*(B+1)
def code : Code := .seq RootFrequency.code
  (.seq RootGrid.coefficientCode (.call (TapeOps.clear 342)))
def costBound (grid N B I : ℕ) : ℕ := RootFrequency.costBound B I+
  RootGrid.coefficientCost grid N (decodedWidth B) I+6*(grid^3).bits.length+4

theorem pair_width (n : ℕ→ℕ) (B : ℕ) (hB : 2≤B)
    (hn : ∀i∈RootFrequency.ids,(n i).bits.length≤B) :
    ∀i∈RootFrequency.ids,(RootFrequency.pair n i).bits.length≤4*(B+1) := by
  have ww := Calibration.ArrayDecodeMachine.nat_values_width RootFrequency.ids RootFrequency.prepare
    RootFrequency.prepare_valid n B hn
    (by simp [RootFrequency.prepare,NatAssign.Instruction.literalWidth,show (2:ℕ).bits.length=2 by rfl];omega)
  have w0 : ∀i∈RootFrequency.ids,(RootFrequency.prepared n i).bits.length≤4*(B+1) := by
    simpa only [RootFrequency.prepared,show RootFrequency.prepare.length=2 by rfl,
      show 2^2=4 by rfl] using ww
  exact Calibration.ArrayDecodeMachine.divModValues_width (RootFrequency.prepared n)
    RootFrequency.ids 330 343 330 341 _ (by decide) w0

theorem decoded_width (n : ℕ→ℕ) (B : ℕ) (hB : 2≤B)
    (hn : ∀i∈RootFrequency.ids,(n i).bits.length≤B) :
    ∀i∈RootFrequency.ids,(RootFrequency.values n i).bits.length≤decodedWidth B := by
  have hw := RootFrequency.tail_width n (4*(B+1)) (pair_width n B hB hn)
  intro i hi
  exact (hw i hi).trans (by unfold decodedWidth;omega)

theorem workspace_subset (S : Finset ℕ) :
    RootFrequency.workspace S⊆RootGrid.coefficientWorkspace S := by
  have dc : RootGrid.decodeWorkspace⊆RootGrid.coefficientWorkspace S :=
    (Finset.subset_union_left.trans Finset.subset_union_right).trans Finset.subset_union_right
  have cc : RootGrid.clockIds⊆RootGrid.coefficientWorkspace S :=
    (Finset.subset_union_right.trans Finset.subset_union_left).trans Finset.subset_union_left
  have fc : RootFrequency.changed⊆RootGrid.decodeWorkspace∪RootGrid.clockIds := by decide
  intro i hi
  rcases Finset.mem_union.mp hi with hi|hi
  · rcases Finset.mem_union.mp (fc hi) with hi|hi
    · exact dc hi
    · exact cc hi
  · exact Finset.mem_union_left _ (Finset.mem_union_right _ hi)

theorem executes (S : Finset ℕ) (hS : RootGrid.coefficientInputs⊆S) (h8 : 8∈S)
    (grid degree N B I : ℕ) [NeZero grid] (hgrid : grid=2*degree+1) (hB : 2≤B) (hI : 1≤I)
    (n : ℕ→ℕ) (initial : ℕ→Parts) (hn331 : n 331=grid)
    (hn : ∀i∈RootFrequency.ids,(n i).bits.length≤B)
    (hz : ∀i∈NaturalQuotient.workPorts,n i=0)
    (hw : WidthBank S I initial) (hg : Good S initial)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hb : NatAssign.Bank RootFrequency.ids n s.val) (hr : Ready S initial s)
    (hblank : ∀i,i<5 → Blank s.val i)
    (hglue : Glue.Clean s.val) (hphase : Phase.Runtime.Clean s.val)
    (hprec : Word s.val 640 N) (hQ : Word s.val 652 1) (hprec' : Word s.val 653 N) :
    ∃cost t,Executes input tape code cost s t ∧ cost≤costBound grid N B I ∧
      Nonempty (RootGrid.CoefficientState S grid N (RootFrequency.frequency grid (n 330))
        (decodedWidth B) I (RootFrequency.parityParts n initial) t) ∧
      Blank t.val 342 ∧ BinaryPrecision.Frame (RootGrid.coefficientWorkspace S) s.val t.val := by
  have hp : 0 < n 331 := by rw [hn331];exact Nat.pos_of_ne_zero (NeZero.ne grid)
  obtain ⟨c0,s0,e0,h0,b0,r0,g0,w0,z0,gl0,ph0,p640,p652,p653,f0⟩ :=
    RootFrequency.code_executes S h8 n initial N B I hB hI hn hw hg hz hp
      input tape s hb hr hblank hglue hphase hprec hQ hprec'
  have wn := decoded_width n B hB hn
  have gn : RootFrequency.values n 331=grid :=
    (RootFrequency.values_keep n 331 (Or.inr (Or.inl rfl))).trans hn331
  have zn (i : ℕ) (hi : i∈NaturalQuotient.workPorts) : RootFrequency.values n i=0 := by
    rw [RootFrequency.values_keep n i (Or.inl hi),hz i hi]
  have hi0 : RootGrid.ids⊆RootFrequency.ids := by decide
  have hi1 : RootGrid.clockIds⊆RootFrequency.ids := by decide
  obtain ⟨c1,s1,e1,h1,⟨state⟩,f1⟩ := RootGrid.coefficient_executes S hS grid N
    (RootFrequency.frequency grid (n 330)) (decodedWidth B) I (by unfold decodedWidth;omega) hI
    (RootFrequency.values n) (RootFrequency.parityParts n initial) gn
    (RootFrequency.values_frequency n grid degree hn331 hgrid) zn
    (fun i hi => wn i (hi0 hi)) (fun i hi => wn i (hi1 hi)) w0 g0 input tape s0 r0
    (fun i hi => b0 i (hi0 hi)) (fun i hi => b0 i (hi1 hi)) z0 gl0 ph0 p640 p652 p653
  obtain ⟨c2,t,out,e2,h2,_,_,z2,f2⟩ := state.clear_executes input tape s1
  have f2' := f2.mono (show ({342}:Finset ℕ)⊆RootGrid.coefficientWorkspace S by
    intro i hi
    have he : i=342 := by simpa only [Finset.mem_singleton] using hi
    subst i
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (by decide)))
  exact ⟨c0+(c1+c2),t,e0.seq (e1.seq e2),by unfold costBound;omega,⟨out⟩,z2,
    (f0.mono (workspace_subset S)).trans (f1.trans f2')⟩

#print axioms executes
end Maxwell.Continuum.RationalDataflow.RootIndexed
