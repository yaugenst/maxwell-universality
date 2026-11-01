import Maxwell.Continuum.CalibrationBasisColumnFrame
import Maxwell.Continuum.CalibrationEdgeController

/-! The executed edge controller changes the radius word and its private
counters. All canonical source/header evidence is rebuilt at that boundary. -/
namespace Maxwell.Continuum.Calibration.BasisColumn
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
set_option maxHeartbeats 2500000
set_option maxRecDepth 16384
attribute [local irreducible] BasisForcing.bank SchurRow.nodeCount

theorem State.rebase {R R' heap P : ℕ} {p : ℕ→Parts} {s t : Store}
    (state : State R heap P p s) (frame : BinaryPrecision.Frame EdgeController.changed s.val t.val)
    (scratch : NatAssign.Scratch t.val) (radius : RationalAccumulator.Word t.val 311 R') :
    State R' heap P p t := by
  have keep (k : ℕ) (low : 4≤k) (high : k<600) (different : k≠311) : t.val.tapes k=s.val.tapes k := by
    apply frame.tapes
    simp only [EdgeController.changed,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.mem_Icc]
    omega
  have parts : Ready BasisScalarReload.bank (BasisScalarReload.values p) t := by
    refine ⟨?_,scratch⟩
    intro k hk
    apply RationalAccumulator.word_of_eq (frame.tapes k ?_) (state.ready.parts.1 k hk)
    rcases Finset.mem_union.mp hk with cell | work
    · obtain ⟨i,_,owned⟩:=Finset.mem_biUnion.mp cell
      have low : 1000≤k := by
        simp only [cellPorts,positivePort,negativePort,denominatorPort,Finset.mem_insert,Finset.mem_singleton] at owned
        omega
      simp only [EdgeController.changed,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.mem_Icc]
      omega
    · simp only [workPorts,temporaryPorts,RationalMagnitude.ids,Finset.mem_union,
        Finset.mem_insert,Finset.mem_singleton] at work
      simp only [EdgeController.changed,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.mem_Icc]
      omega
  have cleaned : ∀k∈BasisReentry.cleanupWords,RationalAccumulator.Blank t.val k := by
    intro k hk
    have bound:=BasisReentry.cleanup_bounds k hk
    exact RationalAccumulator.blank_of_eq (keep k (by omega) bound.2.1 bound.2.2.1) (state.ready.cleared k hk)
  have free : RationalAccumulator.Word t.val 376 heap := by
    apply RationalAccumulator.word_of_eq (keep 376 (by decide) (by decide) (by decide))
    simpa only [BasisReentry.heap] using state.ready.naturals 376 (Finset.mem_union_right _ (by simp))
  have oldBlank (k : ℕ) (low : 5≤k) (high : k≤9) :
      RationalAccumulator.Blank s.val k→RationalAccumulator.Blank t.val k :=
    RationalAccumulator.blank_of_eq (keep k (by omega) (by omega) (by omega))
  have allScratch : BankArray.Scratch t.val :=
    ⟨scratch 0 (by decide),scratch 1 (by decide),scratch 2 (by decide),scratch 3 (by decide),
      oldBlank 5 (by decide) (by decide) state.ready.scratch.2.2.2.2.1,
      oldBlank 6 (by decide) (by decide) state.ready.scratch.2.2.2.2.2.1,
      oldBlank 8 (by decide) (by decide) state.ready.scratch.2.2.2.2.2.2.1,
      oldBlank 9 (by decide) (by decide) state.ready.scratch.2.2.2.2.2.2.2⟩
  exact ⟨BasisReentry.assemble R' heap p t parts cleaned radius free allScratch
    (oldBlank 7 (by decide) (by decide) state.ready.seven),state.good,state.width⟩

#print axioms State.rebase
end Maxwell.Continuum.Calibration.BasisColumn
