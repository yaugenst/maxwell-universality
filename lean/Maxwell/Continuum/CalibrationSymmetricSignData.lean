import Maxwell.Continuum.CalibrationCentralPrepare
import Maxwell.Continuum.DefinitenessExpressionBounds
import Maxwell.Continuum.DefinitenessExpressionMachine
import Maxwell.Continuum.CalibrationMatrixSymmetrization

/-! Symmetrization is part of the compiled expression. The sign circuit uses
the same isolated bank and input copying as the central inverse. -/
namespace Maxwell.Continuum.Calibration.SymmetricSign
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
open ExpressionDefiniteness
set_option maxHeartbeats 1800000
set_option maxRecDepth 16384
attribute [local irreducible] MatrixInverse.registers PolynomialExpression.determinantNodes
  ExpressionDefiniteness.extent

def index (i j : Fin 24) : ℕ := 24*i.val+j.val
def expressions : Matrix (Fin 24) (Fin 24) RationalExpression := fun i j=>
  .binary .sub .zero (.binary .mul (.input 576) (.binary .add (.input (index i j)) (.input (index j i))))
def source (v : ℕ→Parts) : Matrix (Fin 24) (Fin 24) ℚ := fun i j=>(v (index i j)).value
def size : ℕ := MatrixInverse.base 24+2*PolynomialExpression.determinantNodes 24 1+3
def bank : Finset ℕ := Finset.range size

theorem bank_eq : bank=CentralRelocation.bank := by
  unfold bank size CentralRelocation.bank MatrixInverse.registers
  rfl

theorem index_lt (i j : Fin 24) : index i j<576 := by
  have hi:=i.isLt
  have hj:=j.isLt
  unfold index
  omega

theorem small_mem (i : ℕ) (hi : i<1152) : i∈bank := by
  simp only [bank,Finset.mem_range,size]
  have base : MatrixInverse.base 24=1152 := by decide
  rw [base]
  omega

theorem expressions_fit : 578+extent expressions≤size := by
  have h:=extent_bound expressions 7 (fun _ _=>by simp only [expressions,RationalExpression.nodes];decide)
  have bound : 578+9*5^24≤size := by
    simp only [size]
    decide +kernel
  omega

theorem expressions_below : Below expressions 578 := by
  intro i j
  simp only [expressions,RationalExpression.Below]
  exact ⟨trivial,by decide,by have :=index_lt i j;omega,by have :=index_lt j i;omega⟩

theorem expressions_safe (v : ℕ→Parts) (good : Good bank v) : Safe expressions v := by
  intro i j
  exact ⟨trivial,good 576 (small_mem 576 (by decide)),
    good _ (small_mem _ ((index_lt i j).trans (by decide))),
    good _ (small_mem _ ((index_lt j i).trans (by decide)))⟩

theorem expressions_value (v : ℕ→Parts) (good : Good bank v) (half : (v 576).value=1/2) :
    RawDefiniteness.values (evaluate expressions v)=-symmetricRationalMatrix (source v) := by
  ext i j
  have hi:=good _ (small_mem _ ((index_lt i j).trans (by decide)))
  have hj:=good _ (small_mem _ ((index_lt j i).trans (by decide)))
  have hh:=good 576 (small_mem 576 (by decide))
  change ((Parts.literal 0).sub ((v 576).mul ((v (index i j)).add (v (index j i))))).value=_
  rw [Parts.sub_value _ _ (Parts.literal_valid _) (Parts.mul_valid hh (Parts.add_valid hi hj)),
    Parts.literal_value,Parts.mul_value,Parts.add_value _ _ hi hj,half]
  simp only [symmetricRationalMatrix,source,Matrix.neg_apply,Matrix.smul_apply,
    Matrix.add_apply,Matrix.transpose_apply,smul_eq_mul,zero_sub]

#print axioms expressions_fit
#print axioms expressions_value
end Maxwell.Continuum.Calibration.SymmetricSign
