import Maxwell.Continuum.RationalDataflowControl
import Maxwell.Cost.Structured.NatAssign.TapeInterval

/-! The rational compiler preserves disjoint tape intervals even when its
literal arithmetic values are opaque. This avoids evaluating coefficients
merely to certify a machine-state handoff. -/
namespace Maxwell.Continuum.RationalDataflow
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384

private theorem stage_outside (S : Finset ℕ) (lo hi : ℕ) (low : 4 ≤ lo)
    (outside : ∀i∈ids S,i<lo ∨hi ≤ i)
    (stage : List NatAssign.Instruction) (valid : ∀a∈stage,a.Valid (ids S)) :
    (NatAssign.code stage).outsideTapes lo hi=true :=
  NatAssign.code_outside stage (ids S) lo hi valid low outside

theorem inverseCode_outside (S : Finset ℕ) (lo hi : ℕ) (low : 4 ≤ lo)
    (outside : ∀i∈ids S,i<lo ∨hi ≤ i)
    (magnitude : RationalMagnitude.program.outsideTapes lo hi=true)
    (target source : ℕ) (ht : target∈S) (hs : source∈S) :
    (inverseCode target source).outsideTapes lo hi=true := by
  simp only [inverseCode,Code.outsideTapes,Bool.and_eq_true]
  exact ⟨stage_outside S lo hi low outside _ (prepareInverse_valid S source hs),magnitude,
    stage_outside S lo hi low outside _ (inverseTail_valid S true target source ht hs),
    stage_outside S lo hi low outside _ (inverseTail_valid S false target source ht hs)⟩

theorem Instruction.outsideTapes (instruction : Instruction) (S : Finset ℕ) (lo hi : ℕ)
    (valid : instruction.Valid S) (low : 4 ≤ lo) (outside : ∀i∈ids S,i<lo ∨hi ≤ i)
    (magnitude : RationalMagnitude.program.outsideTapes lo hi=true) :
    instruction.code.outsideTapes lo hi=true := by
  cases instruction with
  | literal target value => exact stage_outside S lo hi low outside _ (literalStage_valid S target valid (Parts.literal value))
  | binary op target left right =>
    exact stage_outside S lo hi low outside _ (binaryStage_valid S op target left right valid.1 valid.2.1 valid.2.2)
  | inverse target source => exact inverseCode_outside S lo hi low outside magnitude target source valid.1 valid.2

theorem Control.outsideTapes (control : Control) (S : Finset ℕ) (lo hi : ℕ)
    (valid : control.Valid S) (low : 4 ≤ lo) (outside : ∀i∈ids S,i<lo ∨hi ≤ i)
    (magnitude : RationalMagnitude.program.outsideTapes lo hi=true) :
    control.code.outsideTapes lo hi=true := by
  induction control with
  | done => rfl
  | step a rest ih =>
    simp only [Control.code,Code.outsideTapes,Bool.and_eq_true]
    exact ⟨a.outsideTapes S lo hi valid.1 low outside magnitude,ih valid.2⟩
  | positive source yes no iy ino =>
    have p : (positivePrefix source).outsideTapes lo hi=true := by
      simp only [positivePrefix,Code.outsideTapes,Bool.and_eq_true]
      exact ⟨stage_outside S lo hi low outside _ (preparePositive_valid S source valid.1),magnitude⟩
    have cleanup := stage_outside S lo hi low outside _ (clearMagnitude_valid S)
    simp only [Control.code,Code.outsideTapes,p,cleanup,iy valid.2.1,ino valid.2.2,Bool.and_self]

#print axioms Control.outsideTapes
end Maxwell.Continuum.RationalDataflow
