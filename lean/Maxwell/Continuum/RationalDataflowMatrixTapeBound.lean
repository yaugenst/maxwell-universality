import Maxwell.Continuum.RationalDataflowTapeBound
import Maxwell.Continuum.RationalDataflowMatrixInversePlan

/-! The fixed inverse compiler fits a symbolic finite tape interval; this
does not enumerate its factorial-sized determinant syntax. -/
namespace Maxwell.Continuum.RationalDataflow.MatrixInverse
open Maxwell.Cost Maxwell.Cost.Structured

def tapeBound (n : ℕ) : ℕ := 1000+3*(base n+2*PolynomialExpression.determinantNodes n 1+3)

theorem control_tapeBound (n : ℕ) : (control n).code.tapeBound≤ tapeBound n := by
  exact Control.tapeBound_le _ (registers n) _ (traversal_valid n (coordinates n))
    (fun _ hi => Finset.mem_range.mp hi)

theorem control_protects (n i : ℕ) (outside : tapeBound n≤ i) :
    (control n).code.protectsTape i=true :=
  Code.protectsTape_of_bound _ i ((control_tapeBound n).trans outside)

#print axioms control_tapeBound
end Maxwell.Continuum.RationalDataflow.MatrixInverse
