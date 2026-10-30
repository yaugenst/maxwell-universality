import Maxwell.Continuum.CalibrationRootGridFacts
import Maxwell.Continuum.CalibrationRootGridGood
import Maxwell.Continuum.CalibrationRootGridSums
import Maxwell.Continuum.RationalDataflowSizedCounted

/-! The countdown invariant records the actual rational bank, its derived
raw width, and the exact sum of samples already visited. -/
namespace Maxwell.Continuum.RationalDataflow.RootGrid
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 3000000

def dataWidth (B I : ℕ) : ℕ := naturalWidth B+I
def summandWidth (N B I : ℕ) : ℕ := coefficientBankWidth N (dataWidth B I)
def initialWidth (N B I : ℕ) : ℕ := 10+N.bits.length+dataWidth B I+summandWidth N B I
def loopWidth (grid N B I remaining : ℕ) : ℕ :=
  initialWidth N B I+(grid^3-remaining)*(summandWidth N B I+1)

def realSummand (grid N : ℕ) (frequency : Fin 3→ℤ) (initial : ℕ→Parts) (index : ℕ) : ℚ :=
  (Calibration.rootProductSample grid (initial 9).value N frequency (point grid index)).re.center
def imagSummand (grid N : ℕ) (frequency : Fin 3→ℤ) (initial : ℕ→Parts) (index : ℕ) : ℚ :=
  (Calibration.rootProductSample grid (initial 9).value N frequency (point grid index)).im.center

structure LoopState (S : Finset ℕ) (grid N : ℕ) (frequency : Fin 3→ℤ) (B I : ℕ)
    (initial : ℕ→Parts) (remaining : ℕ) (s : Store) where
  naturals : ℕ→ℕ
  parts : ℕ→Parts
  remaining_le : remaining≤grid^3
  facts : InputFacts grid frequency B naturals
  natural_bank : NatAssign.Bank ids naturals s.val
  rational_bank : Ready S parts s
  good : Good S parts
  width : WidthBank S (loopWidth grid N B I remaining) parts
  external : ∀i,8 ≤ i → i≠10 → i≠11 → parts i=initial i
  real_value : (parts 10).value=(initial 10).value+tailSum (realSummand grid N frequency initial) (grid^3) remaining
  imag_value : (parts 11).value=(initial 11).value+tailSum (imagSummand grid N frequency initial) (grid^3) remaining
  scratch : ∀i,i<5 → Blank s.val i
  glue : Glue.Clean s.val
  phase : Phase.Runtime.Clean s.val
  precision_glue : Word s.val 640 N
  phase_range : Word s.val 652 1
  precision_phase : Word s.val 653 N

theorem loopWidth_ge (grid N B I remaining : ℕ) :
    10≤loopWidth grid N B I remaining ∧ N.bits.length≤loopWidth grid N B I remaining ∧
      dataWidth B I≤loopWidth grid N B I remaining ∧ summandWidth N B I≤loopWidth grid N B I remaining := by
  unfold loopWidth initialWidth
  omega

theorem loopWidth_step (grid N B I remaining : ℕ) (hr : remaining<grid^3) :
    loopWidth grid N B I (remaining+1)+summandWidth N B I+1=loopWidth grid N B I remaining := by
  have he : grid^3-remaining=(grid^3-(remaining+1))+1 := by omega
  unfold loopWidth
  rw [he,Nat.add_mul]
  omega

theorem loopWidth_le_final (grid N B I remaining : ℕ) :
    loopWidth grid N B I remaining≤loopWidth grid N B I 0 := by
  apply Nat.add_le_add_left
  exact Nat.mul_le_mul_right _ (by omega)

theorem counter_outside (S : Finset ℕ) : 342∉sampleWorkspace S := by
  have hr := FractionWord.outside S 342 (by decide)
  have hg : 342∉GlueMachine.Runtime.ids := by decide
  have hp : 342∉PhaseMachine.Runtime.ids := by decide
  have hd : 342∉decodeWorkspace := by decide
  simp only [sampleWorkspace,Finset.mem_union,not_or]
  refine ⟨hd,?_⟩
  simp only [RootProduct.workspace,Glue.workspace,Glue.allIds,Phase.Runtime.workspace,
    Phase.Runtime.allIds,RationalDataflow.workspace,Finset.mem_union] at *
  tauto

def LoopState.count_frame {S : Finset ℕ} {grid N : ℕ} {frequency : Fin 3→ℤ} {B I : ℕ}
    {initial : ℕ→Parts} {remaining : ℕ} {s t : Store}
    (h : LoopState S grid N frequency B I initial remaining s)
    (f : CountedShifted.Frame 342 s t) : LoopState S grid N frequency B I initial remaining t where
  naturals := h.naturals
  parts := h.parts
  remaining_le := h.remaining_le
  facts := h.facts
  natural_bank i hi := word_of_eq (f.2.2.2.2.2.1 i (by have := ids_bounds i hi;omega)) (h.natural_bank i hi)
  rational_bank := Ready.count_frame S h.parts 342 (FractionWord.outside S 342 (by decide)) h.rational_bank f
  good := h.good
  width := h.width
  external := h.external
  real_value := h.real_value
  imag_value := h.imag_value
  scratch i hi := blank_of_eq (f.2.2.2.2.2.1 i (by omega)) (h.scratch i hi)
  glue i hi := blank_of_eq (f.2.2.2.2.2.1 i (by
    intro he;subst i;exact (show 342∉GlueMachine.Runtime.ids.erase 640 by decide) hi)) (h.glue i hi)
  phase i hi := blank_of_eq (f.2.2.2.2.2.1 i (by
    intro he;subst i;exact (show 342∉(PhaseMachine.Runtime.ids.erase 652).erase 653 by decide) hi)) (h.phase i hi)
  precision_glue := word_of_eq (f.2.2.2.2.2.1 640 (by decide)) h.precision_glue
  phase_range := word_of_eq (f.2.2.2.2.2.1 652 (by decide)) h.phase_range
  precision_phase := word_of_eq (f.2.2.2.2.2.1 653 (by decide)) h.precision_phase

#print axioms LoopState.count_frame
end Maxwell.Continuum.RationalDataflow.RootGrid
