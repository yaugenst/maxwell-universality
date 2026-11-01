import Maxwell.Continuum.CalibrationBasisReentryMachine
import Maxwell.Cost.Structured.WordCleanupBounds

/-! The restart budget comes from the words returned by the executed
column. No zeroed header or fresh array workspace is assumed here. -/
namespace Maxwell.Continuum.Calibration.BasisReentry
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.CalibrationMatrix
open RationalDataflow ArrayDecodeMachine NeumannMachine
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384
attribute [local irreducible] BasisForcing.bank SchurRow.nodeCount

theorem cleanup_bounded (s : Store) (B₁ B₂ B₃ B₄ B₅ B₆ B₇ : ℕ)
    (descriptors : ∃n,NatAssign.Bank Descriptors.retainedIds n s.val ∧
      ∀k∈Descriptors.retainedIds,(n k).bits.length≤B₁)
    (controls : ∃n,NatAssign.Bank (Finset.Icc 311 332) n s.val ∧
      ∀k∈Finset.Icc 311 332,(n k).bits.length≤B₂)
    (retired : WordCleanup.Bounded conversionRetiredWords B₃ s.val)
    (allocator : ∃n,NatAssign.Bank CoefficientAllocation.workIds n s.val ∧
      ∀k∈CoefficientAllocation.workIds,(n k).bits.length≤B₄)
    (inactive : ∃n,NatAssign.Bank AllocatedInverse.inactiveIds n s.val ∧
      ∀k∈AllocatedInverse.inactiveIds,(n k).bits.length≤B₅)
    (active : WordCleanup.Bounded Horner.activeCleanup B₆ s.val)
    (readout : WordCleanup.Bounded SchurReadColumn.readoutWords B₇ s.val) :
    WordCleanup.Bounded cleanupWords (B₁+B₂+B₃+B₄+B₅+B₆+B₇) s.val := by
  obtain ⟨n₁,s₁,w₁⟩:=descriptors
  obtain ⟨n₂,s₂,w₂⟩:=controls
  obtain ⟨n₄,s₄,w₄⟩:=allocator
  obtain ⟨n₅,s₅,w₅⟩:=inactive
  have d:=WordCleanup.Bounded.of_bank s₁ w₁
  have a:=WordCleanup.Bounded.of_bank s₄ w₄
  have i:=WordCleanup.Bounded.of_bank s₅ w₅
  have c : WordCleanup.Bounded ((Finset.Icc 312 332).sort (·≤·)) B₂ s.val := by
    intro k hk
    have member : k∈Finset.Icc 311 332 := by
      have := (Finset.mem_sort _).mp hk
      simp only [Finset.mem_Icc] at this ⊢
      omega
    exact ⟨(n₂ k).bits,w₂ k member,s₂ k member⟩
  exact ((((((d.append c).append retired).append a).append i).append active).append readout).mono (by omega)

#print axioms cleanup_bounded
end Maxwell.Continuum.Calibration.BasisReentry
