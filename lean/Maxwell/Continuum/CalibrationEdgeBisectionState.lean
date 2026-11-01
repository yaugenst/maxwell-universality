import Maxwell.Continuum.CalibrationEdgeTestMachine
import Maxwell.Continuum.CalibrationBasisColumnRadius

/-! Concrete retained state of the certified edge loop. Widths record actual
stored words; all matrix and scalar cells are produced by the loop body. -/
namespace Maxwell.Continuum.Calibration.EdgeBisection
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow CentralRelocation
set_option maxHeartbeats 2500000
set_option maxRecDepth 16384
attribute [local irreducible] CentralRelocation.bank count gap relocation
  MatrixInverse.tapeBound MatrixInverse.registers PolynomialExpression.determinantNodes

structure Data where
  scalar : ℕ → Parts
  bracket : ℕ → ℕ
  control : ℕ → ℕ
  central : ℕ → Parts
  scalarWidth : ℕ
  bracketWidth : ℕ
  controlWidth : ℕ
  centralWidth : ℕ

structure Ready (target heap k : ℕ) (d : Data) (s : Store) : Prop where
  basis : BasisColumn.State (193+k) heap d.scalarWidth d.scalar s
  bracket : NatAssign.Bank (SignedBracket.ids EdgeBracketMachine.base) d.bracket s.val
  bracketWidth : ∀i∈SignedBracket.ids EdgeBracketMachine.base,(d.bracket i).bits.length ≤ d.bracketWidth
  bracketPositive : 7 ≤ d.bracketWidth
  represents : EdgeBracketMachine.Represents d.bracket (edgeBrackets edgeDecision 182 edgeInitial k)
  controller : NatAssign.Bank EdgeController.activeIds d.control s.val
  controllerWidth : ∀i∈EdgeController.activeIds,(d.control i).bits.length ≤ d.controlWidth
  precision : d.control 850=188+k
  remaining : d.control 851=2*target-k
  radius : d.control 311=193+k
  bounded : k ≤ 2*target
  machin : EdgeScalar.RelocatedFresh s.val
  central : RationalDataflow.Ready bank d.central (s.renameTapes relocation)
  centralWidth : WidthBank bank d.centralWidth d.central
  centralPositive : 1 ≤ d.centralWidth

def bracketWork : Finset ℕ := {0,1,2,3}∪SignedBracket.ids EdgeBracketMachine.base

theorem bracket_bounds (i : ℕ) (hi : i∈SignedBracket.ids EdgeBracketMachine.base) :
    7900 ≤ i ∧ i<7912 := by
  simpa only [SignedBracket.ids,EdgeBracketMachine.base,positivePort,Finset.mem_Ico] using hi

theorem bracket_outside (i : ℕ) (positive : 4 ≤ i) (outside : i<7900 ∨ 7912 ≤ i) : i∉bracketWork := by
  simp only [bracketWork,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
  intro h
  rcases h with small | large
  · omega
  · have := bracket_bounds i large;omega

theorem controller_bounds (i : ℕ) (hi : i∈EdgeController.activeIds) :
    i=311 ∨ 850 ≤ i ∧ i<860 := by
  simp only [EdgeController.activeIds,Finset.mem_union,Finset.mem_singleton,Finset.mem_Icc] at hi
  omega

theorem controller_outside (i : ℕ) (positive : 4 ≤ i) (different : i≠311)
    (outside : i<850 ∨ 860 ≤ i) : i∉EdgeController.changed := by
  simp only [EdgeController.changed,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.mem_Icc]
  omega

theorem bracket_basis {R heap P : ℕ} {p : ℕ → Parts} {s t : Store}
    (state : BasisColumn.State R heap P p s) (frame : BinaryPrecision.Frame bracketWork s.val t.val)
    (scratch : NatAssign.Scratch t.val) : BasisColumn.State R heap P p t :=
  state.transfer (fun i lo hi=>frame.tapes i (bracket_outside i lo (Or.inl (by omega)))) scratch

theorem bracket_controller {v : ℕ → ℕ} {s t : Store}
    (stored : NatAssign.Bank EdgeController.activeIds v s.val)
    (frame : BinaryPrecision.Frame bracketWork s.val t.val) :
    NatAssign.Bank EdgeController.activeIds v t.val := by
  intro i hi
  have bounds:=controller_bounds i hi
  exact RationalAccumulator.word_of_eq
    (frame.tapes i (bracket_outside i (by omega) (Or.inl (by omega)))) (stored i hi)

theorem bracket_machin {s t : Store} (fresh : EdgeScalar.RelocatedFresh s.val)
    (frame : BinaryPrecision.Frame bracketWork s.val t.val) : EdgeScalar.RelocatedFresh t.val := by
  intro i lo hi
  exact RationalAccumulator.blank_of_eq
    (frame.tapes i (bracket_outside i (by omega) (Or.inl (by omega)))) (fresh i lo hi)

theorem bracket_central {v : ℕ → Parts} {s t : Store}
    (stored : RationalDataflow.Ready bank v (s.renameTapes relocation))
    (frame : BinaryPrecision.Frame bracketWork s.val t.val) (scratch : NatAssign.Scratch t.val) :
    RationalDataflow.Ready bank v (t.renameTapes relocation) := by
  apply BasisMatrixSign.central_retained v s t stored _ scratch
  intro i hi
  exact frame.tapes i (bracket_outside i (by unfold gap count at hi;omega)
    (Or.inr (by unfold gap count at hi;omega)))

theorem controller_bracket {v : ℕ → ℕ} {s t : Store}
    (stored : NatAssign.Bank (SignedBracket.ids EdgeBracketMachine.base) v s.val)
    (frame : BinaryPrecision.Frame EdgeController.changed s.val t.val) :
    NatAssign.Bank (SignedBracket.ids EdgeBracketMachine.base) v t.val := by
  intro i hi
  have bounds:=bracket_bounds i hi
  exact RationalAccumulator.word_of_eq
    (frame.tapes i (controller_outside i (by omega) (by omega) (Or.inr (by omega)))) (stored i hi)

theorem controller_machin {s t : Store} (fresh : EdgeScalar.RelocatedFresh s.val)
    (frame : BinaryPrecision.Frame EdgeController.changed s.val t.val) : EdgeScalar.RelocatedFresh t.val := by
  intro i lo hi
  exact RationalAccumulator.blank_of_eq
    (frame.tapes i (controller_outside i (by omega) (by omega) (Or.inr (by omega)))) (fresh i lo hi)

theorem controller_central {v : ℕ → Parts} {s t : Store}
    (stored : RationalDataflow.Ready bank v (s.renameTapes relocation))
    (frame : BinaryPrecision.Frame EdgeController.changed s.val t.val) (scratch : NatAssign.Scratch t.val) :
    RationalDataflow.Ready bank v (t.renameTapes relocation) := by
  apply BasisMatrixSign.central_retained v s t stored _ scratch
  intro i hi
  have low : 10000 ≤ i := by unfold gap count at hi;omega
  exact frame.tapes i (controller_outside i (by omega) (by omega) (Or.inr (by omega)))

theorem Ready.transfer {target heap k : ℕ} {d : Data} {s t : Store}
    (state : Ready target heap k d s) (frame : BinaryPrecision.Frame ∅ s.val t.val) :
    Ready target heap k d t := by
  have keep (i : ℕ) : t.val.tapes i=s.val.tapes i := frame.tapes i (by simp)
  have scratch : NatAssign.Scratch t.val := fun i hi=>
    RationalAccumulator.blank_of_eq (keep i) (state.basis.ready.parts.2 i hi)
  exact ⟨state.basis.transfer (fun i _ _=>keep i) scratch,
    fun i hi=>RationalAccumulator.word_of_eq (keep i) (state.bracket i hi),
    state.bracketWidth,state.bracketPositive,state.represents,
    fun i hi=>RationalAccumulator.word_of_eq (keep i) (state.controller i hi),
    state.controllerWidth,state.precision,state.remaining,state.radius,state.bounded,
    fun i lo hi=>RationalAccumulator.blank_of_eq (keep i) (state.machin i lo hi),
    BasisMatrixSign.central_retained d.central s t state.central (fun i _=>keep i) scratch,
    state.centralWidth,state.centralPositive⟩

#print axioms Ready.transfer
end Maxwell.Continuum.Calibration.EdgeBisection
