import Maxwell.Composition.SourceSubdivision
import Maxwell.Composition.SourceDecoration

/-! Exact rational right-hand sides on the actual routed and decorated
vertices. These are finite conditional formulas, with no rounding of g. -/
namespace Maxwell.Composition.SourceRational
open Maxwell.Logical

/-- The only nonzero square-circuit source entries are its original input rows. -/
def boundary (S : Source.SparseSystem) (precision : ℕ)
    (j : Fin (sourceCircuit S precision).size) : ℚ :=
  if hj : j.val < S.n then Normalization.normalizedSource S ⟨j.val,hj⟩ else 0

def positive (S : Source.SparseSystem) (precision : ℕ) : SourcePositive.Vertex S precision → ℚ
  | .inl (.inl j) => boundary S precision j
  | .inl (.inr _) => 0
  | .inr _ => 0

def routed (S : Source.SparseSystem) (precision : ℕ) : SourceRouting.Vertex S precision → ℚ
  | .inl v => positive S precision v
  | .inr _ => 0

def decorated (S : Source.SparseSystem) (precision : ℕ) : SourceDecoration.Vertex S precision → ℚ
  | .inl v => routed S precision v
  | .inr _ => 0

theorem boundary_cast (S : Source.SparseSystem) (precision : ℕ)
    (j : Fin (sourceCircuit S precision).size) :
    (boundary S precision j : ℝ) = SourceResidual.sourceBoundary S precision
      (Source.rationalVector (Normalization.normalizedSource S)) j := by
  by_cases hj : j.val < S.n
  · let i : Fin S.n := ⟨j.val,hj⟩
    have he : (sourceCircuit S precision).circuit.inputIndex i = j :=
      Fin.ext ((sourceCircuit S precision).circuit.inputIndex_value i)
    rw [← he, SourceResidual.sourceBoundary_input]
    change (boundary S precision ((sourceCircuit S precision).circuit.inputIndex i) : ℝ) = _
    simp only [boundary, (sourceCircuit S precision).circuit.inputIndex_value, i, hj, ↓reduceDIte]
    rfl
  · rw [SourceResidual.sourceBoundary_noninput S precision _ j (by omega)]
    simp [boundary,hj]

theorem positive_cast (S : Source.SparseSystem) (precision : ℕ) (v : SourcePositive.Vertex S precision) :
    (positive S precision v : ℝ) = PositiveRecovery.source S precision v := by
  cases v with
  | inl v => cases v with
    | inl j => exact boundary_cast S precision j
    | inr j => exact Rat.cast_zero
  | inr e => exact Rat.cast_zero

theorem routed_cast (S : Source.SparseSystem) (precision : ℕ) (v : SourceRouting.Vertex S precision) :
    (routed S precision v : ℝ) = SourceSubdivision.source S precision v := by
  cases v with
  | inl v => exact positive_cast S precision v
  | inr v => exact Rat.cast_zero

theorem routed_vector (S : Source.SparseSystem) (precision : ℕ) :
    WithLp.toLp 2 (fun v => (routed S precision v : ℝ)) = SourceSubdivision.source S precision := by
  ext v
  exact routed_cast S precision v

theorem decorated_cast (S : Source.SparseSystem) (precision : ℕ) (v : SourceDecoration.Vertex S precision) :
    (decorated S precision v : ℝ) =
      sumLeftInjection (κ := SourceIncidence.E S precision) (SourceSubdivision.source S precision) v := by
  cases v with
  | inl v => exact routed_cast S precision v
  | inr v => exact Rat.cast_zero

theorem decorated_vector (S : Source.SparseSystem) (precision : ℕ) :
    WithLp.toLp 2 (fun v => (decorated S precision v : ℝ)) =
      sumLeftInjection (κ := SourceIncidence.E S precision) (SourceSubdivision.source S precision) := by
  ext v
  exact decorated_cast S precision v

end Maxwell.Composition.SourceRational
