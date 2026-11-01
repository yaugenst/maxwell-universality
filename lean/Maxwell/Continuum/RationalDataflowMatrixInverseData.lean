import Maxwell.Continuum.RationalDataflowDeterminant
import Maxwell.Continuum.RationalDataflowQuotientExpression

/-! Symbolic determinant and adjugate circuits for a matrix stored in a
contiguous rational register bank. No numerical inverse is an input. -/
namespace Maxwell.Continuum.RationalDataflow.MatrixInverse
open PolynomialExpression
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

def index (n : ℕ) : (Fin n×Fin n)≃Fin (n*n) := finProdFinEquiv
def source (n : ℕ) (v : ℕ→ℚ) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => v (index n (i,j)).val
def entries (n : ℕ) : Matrix (Fin n) (Fin n) PolynomialExpression :=
  fun i j => .inputRegister (index n (i,j)).val
def cofactorEntries (n : ℕ) (i j : Fin n) : Matrix (Fin n) (Fin n) PolynomialExpression :=
  (entries n).updateRow j (fun k => .literal (if k=i then 1 else 0))
def denominator (n : ℕ) : PolynomialExpression := determinant n (entries n)
def numerator (n : ℕ) (i j : Fin n) : PolynomialExpression := determinant n (cofactorEntries n i j)
def base (n : ℕ) : ℕ := 2*(n*n)
def output (n : ℕ) (i j : Fin n) : ℕ := n*n+(index n (i,j)).val
def entryControl (n : ℕ) (i j : Fin n) : Control :=
  QuotientExpression.control (numerator n i j) (denominator n) (base n)

theorem output_lt (n : ℕ) (i j : Fin n) : output n i j<base n := by
  have h := (index n (i,j)).isLt
  unfold output base
  omega

theorem source_eq_of_small (n : ℕ) (v w : ℕ→ℚ) (h : ∀i,i<n*n→ v i=w i) :
    source n v=source n w := by
  ext i j
  exact h _ (index n (i,j)).isLt

theorem entries_evaluate (n : ℕ) (v : ℕ→ℚ) :
    (entries n).map (fun e => e.evaluate v)=source n v := rfl

theorem cofactor_evaluate (n : ℕ) (i j : Fin n) (v : ℕ→ℚ) :
    (cofactorEntries n i j).map (fun e => e.evaluate v)=
      (source n v).updateRow j (Pi.single i 1) := by
  ext row col
  by_cases same : row=j
  · subst row
    simp [cofactorEntries,Matrix.updateRow_apply,Matrix.map_apply,PolynomialExpression.evaluate,Pi.single_apply]
  · simp [cofactorEntries,Matrix.updateRow_apply,Matrix.map_apply,same,entries,source,PolynomialExpression.evaluate]

theorem denominator_value (n : ℕ) (v : ℕ→ℚ) :
    (denominator n).evaluate v=(source n v).det := by
  rw [denominator,determinant_evaluate,entries_evaluate]

theorem numerator_value (n : ℕ) (i j : Fin n) (v : ℕ→ℚ) :
    (numerator n i j).evaluate v=(source n v).adjugate i j := by
  rw [numerator,determinant_evaluate,cofactor_evaluate,Matrix.adjugate_apply]

theorem denominator_scoped (n : ℕ) : (denominator n).Scoped (n*n) :=
  determinant_scoped n (entries n) (n*n) (fun i j => (index n (i,j)).isLt)

theorem cofactor_scoped (n : ℕ) (i j row col : Fin n) :
    (cofactorEntries n i j row col).Scoped (n*n) := by
  by_cases same : row=j
  · subst row
    simp [cofactorEntries,Matrix.updateRow_apply,Scoped]
  · simpa only [cofactorEntries,Matrix.updateRow_apply,ite_eq_right same,entries,Scoped] using
      (index n (row,col)).isLt

theorem numerator_scoped (n : ℕ) (i j : Fin n) : (numerator n i j).Scoped (n*n) :=
  determinant_scoped n (cofactorEntries n i j) (n*n) (cofactor_scoped n i j)

theorem cofactor_literals (n : ℕ) (i j row col : Fin n) (B : ℕ) (hB : 1≤B) :
    (cofactorEntries n i j row col).LiteralsFit B := by
  by_cases same : row=j
  · subst row
    simp only [cofactorEntries,Matrix.updateRow_apply,ite_true,LiteralsFit]
    split_ifs
    · exact (show (Parts.literal 1).Width 1 by change 1≤1 ∧ 0≤1 ∧ 1≤1;omega).mono hB
    · exact (show (Parts.literal 0).Width 1 by change 0≤1 ∧ 0≤1 ∧ 1≤1;omega).mono hB
  · simp [cofactorEntries,Matrix.updateRow_apply,same,entries,LiteralsFit]

theorem numerator_literals (n : ℕ) (i j : Fin n) (B : ℕ) (hB : 1≤B) :
    (numerator n i j).LiteralsFit B :=
  determinant_literals n (cofactorEntries n i j) B hB (fun row col => cofactor_literals n i j row col B hB)

theorem denominator_literals (n B : ℕ) (hB : 1≤B) : (denominator n).LiteralsFit B :=
  determinant_literals n (entries n) B hB (fun _ _ => trivial)

theorem numerator_nodes (n : ℕ) (i j : Fin n) : (numerator n i j).nodes≤determinantNodes n 1 := by
  apply determinant_nodes n (cofactorEntries n i j) 1
  intro row col
  by_cases same : row=j
  · subst row
    simp [cofactorEntries,Matrix.updateRow_apply,nodes]
  · simp [cofactorEntries,Matrix.updateRow_apply,same,entries,nodes]

theorem denominator_nodes (n : ℕ) : (denominator n).nodes≤determinantNodes n 1 :=
  determinant_nodes n (entries n) 1 (fun _ _ => le_rfl)

theorem entry_value (n : ℕ) (i j : Fin n) (v : ℕ→ℚ) :
    (entryControl n i j).rationalEvaluate v (base n)=
      (source n v).det⁻¹*(source n v).adjugate i j := by
  have hbase : n*n≤base n := by unfold base;omega
  have result := (QuotientExpression.rational_result (numerator n i j) (denominator n) (base n)
    ((numerator_scoped n i j).mono hbase) ((denominator_scoped n).mono hbase) v).1
  exact result.trans (by rw [numerator_value,denominator_value,mul_comm])

#print axioms entry_value
#print axioms numerator_nodes
end Maxwell.Continuum.RationalDataflow.MatrixInverse
