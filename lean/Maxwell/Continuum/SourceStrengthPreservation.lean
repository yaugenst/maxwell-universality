import Maxwell.Continuum.SourceStrengthTables

/-! Routing and chronological geometry write above the source prefix.
The exact saved source diagonal and degree arrays therefore remain valid
inputs to the physical strength arithmetic. -/
noncomputable section
namespace Maxwell.Continuum.SourceStrengthTables
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Composition
open SourceGraph.Positive
set_option maxHeartbeats 2000000

theorem Represents.prefix {S : Source.SparseSystem} {p : ℕ}
    {old new : ℕ→Bool} (h : Represents S p old)
    (keep : ∀a, a<base S p+4*(2*dimension S p+count S p)→new a=old a) :
    Represents S p new := by
  constructor
  · refine ⟨h.diagonal.length,?_⟩
    intro i j hj
    rw [keep]
    · exact h.diagonal.bits i j hj
    · have hi := i.isLt
      dsimp [dimension,count]
      omega
  · refine ⟨h.counter.length,?_⟩
    intro i j hj
    rw [keep]
    · exact h.counter.bits i j hj
    · have hi := i.isLt
      dsimp [base]
      omega

#print axioms Represents.prefix
end Maxwell.Continuum.SourceStrengthTables
