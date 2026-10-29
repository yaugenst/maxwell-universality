import Maxwell.Composition.PositiveRecovery

/-! The exact normalized rational right-hand side is inserted isometrically
into the positive graph. Its amplitude obeys the physical convention `G ≥ 1`
without an extra logical right-hand-side rounding stage. -/

noncomputable section

namespace Maxwell.Composition.SourceAmplitude

open Maxwell.Logical

/-- The actual graph source satisfies the physical `G ≥ 1` convention. -/
theorem source_norm_ge_one (S : Source.SparseSystem) (hb : S.source ≠ 0)
    (precision : ℕ) : 1 ≤ ‖PositiveRecovery.source S precision‖ := by
  rw [PositiveRecovery.source_norm]
  exact Normalization.normalizedSource_norm_ge_one S hb

theorem source_norm_le_sqrt (S : Source.SparseSystem) (hb : S.source ≠ 0)
    (precision : ℕ) : ‖PositiveRecovery.source S precision‖ ≤ Real.sqrt (S.n : ℝ) := by
  rw [PositiveRecovery.source_norm]
  exact Normalization.normalizedSource_norm_le S hb

theorem source_norm_bounds (S : Source.SparseSystem) (hb : S.source ≠ 0)
    (precision : ℕ) :
    1 ≤ ‖PositiveRecovery.source S precision‖ ∧
      ‖PositiveRecovery.source S precision‖ ≤ Real.sqrt (S.n : ℝ) :=
  ⟨source_norm_ge_one S hb precision, source_norm_le_sqrt S hb precision⟩

end Maxwell.Composition.SourceAmplitude
