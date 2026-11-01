import Maxwell.Continuum.RationalDataflowExpressionBounds
import Maxwell.Continuum.CalibrationBasisForcingData
import Maxwell.Continuum.CalibrationCachedSchur

/-! Fixed rational arithmetic combines the retained physical scalars with
the six actually read inverse neighbors to form a central Schur entry. -/
namespace Maxwell.Continuum.Calibration.SchurExpression
open FreeFiber RationalDataflow PolynomialExpression BasisForcing
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

def direction (row : Fin 24) (j : Fin 3) : PolynomialExpression :=
  .binary .add (.literal ((corner row j:ℚ)+1/2)) (.inputRegister (234+j.val))
def square (e : PolynomialExpression) : PolynomialExpression := .binary .mul e e
def block (row : Fin 24) (j : Fin 3) : PolynomialExpression :=
  .binary .sub
    (.binary .mul
      (.binary .sub (.binary .mul (square (.inputRegister 232)) (sum3 (fun k=>square (direction row k))))
        (.inputRegister 233))
      (.literal (if polarization row=j then 1 else 0)))
    (.binary .mul (.binary .mul (.inputRegister 232) (direction row (polarization row)))
      (.binary .mul (.inputRegister 232) (direction row j)))
def central (row column : Fin 24) : PolynomialExpression :=
  .binary .sub
    (sum3 (fun j=>.binary .mul (block row j) (.literal (rationalBasisField column (corner row) j))))
    (.literal (rationalAmplitude*rationalPotential (rationalBasisField column) (corner row) (polarization row)))
def neighbor (row : Fin 24) (j : Fin 3) (plus : Bool) : Alias :=
  if plus then corner row+unitAlias j else corner row-unitAlias j
def neighborRegister (row : Fin 24) (j : Fin 3) (plus : Bool) : ℕ := 240+6*row.val+2*j.val+(if plus then 0 else 1)
def selected (row : Fin 24) (j : Fin 3) (plus : Bool) : PolynomialExpression :=
  .binary .mul (.literal (if rationalCentralCheck (neighbor row j plus) then 0 else 1))
    (.inputRegister (neighborRegister row j plus))
def expression (row column : Fin 24) : PolynomialExpression :=
  .binary .add (central row column)
    (.binary .mul (.literal rationalAmplitude)
      (sum3 (fun j=>.binary .mul (.literal (rationalWeight j))
        (.binary .add (selected row j true) (selected row j false)))))

theorem neighbor_bounds (row : Fin 24) (j : Fin 3) (plus : Bool) :
    ∀k,|neighbor row j plus k|≤2 := by
  intro k
  have cornerBound:(corner row k=-1 ∨ corner row k=0):=by
    unfold corner rationalCubeAlias
    split_ifs <;> omega
  have unitBound:unitAlias j k=0 ∨ unitAlias j k=1:=by
    simp only [unitAlias,Pi.single_apply]
    split_ifs <;> omega
  cases plus <;> simp only [neighbor,Bool.false_eq_true,↓reduceIte,Pi.add_apply,Pi.sub_apply]
  all_goals rcases cornerBound with h|h <;> rcases unitBound with h'|h' <;> rw [h,h'] <;> norm_num

theorem direction_value (row : Fin 24) (v : ℕ→ℚ) (j : Fin 3) :
    (direction row j).evaluate v=rationalDirection (fun k=>v (234+k.val)) (corner row) j := by
  rfl

theorem block_value (row : Fin 24) (v : ℕ→ℚ) (j : Fin 3) :
    (block row j).evaluate v=rationalBlockMatrix (v 232) (v 233)
      (rationalDirection (fun k=>v (234+k.val)) (corner row)) (polarization row) j := by
  simp only [block,PolynomialExpression.evaluate,binaryValue,evaluate_sum3,square,direction_value,rationalBlockMatrix,
    Matrix.sub_apply,Matrix.smul_apply,Matrix.one_apply,Matrix.vecMulVec_apply,smul_eq_mul,pow_two]

theorem central_value (row column : Fin 24) (v : ℕ→ℚ) :
    (central row column).evaluate v=rationalCentralMaterial (v 232) (v 233)
      (fun k=>v (234+k.val)) (rationalBasisField column) (corner row) (polarization row) := by
  simp only [central,PolynomialExpression.evaluate,binaryValue,evaluate_sum3,block_value,rationalCentralMaterial,
    rationalCentralApply,corner_central,↓reduceIte,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,
    basis_central,rationalCentral]

theorem value (row column : Fin 24) (v : ℕ→ℚ) (f : Alias→Fin 3→ℚ)
    (read : ∀j plus,v (neighborRegister row j plus)=f (neighbor row j plus) (polarization row)) :
    (expression row column).evaluate v=rationalCentralMaterial (v 232) (v 233)
        (fun k=>v (234+k.val)) (rationalBasisField column) (corner row) (polarization row)-
      rationalLeftCoupling f (corner row) (polarization row) := by
  simp only [expression,PolynomialExpression.evaluate,binaryValue,central_value,evaluate_sum3,selected,read,
    rationalLeftCoupling,Pi.smul_apply,smul_eq_mul,rationalCentral,corner_central,↓reduceIte,
    rationalPotential,rationalNoncentral,neighbor,Bool.false_eq_true]
  rw [neg_mul,sub_neg_eq_add]
  congr 1
  apply congrArg (fun x:ℚ=>rationalAmplitude*x)
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp

theorem expression_scoped (row column : Fin 24) : (expression row column).Scoped 1200 := by
  have directionScope (j : Fin 3) : (direction row j).Scoped 1200:=by
    change True ∧ 234+j.val<1200
    exact ⟨trivial,by omega⟩
  have blockScope (j : Fin 3) : (block row j).Scoped 1200:=by
    simp only [block,Scoped,square]
    refine ⟨⟨⟨⟨⟨by decide,by decide⟩,?_⟩,by decide⟩,trivial⟩,
      ⟨by decide,directionScope _⟩,by decide,directionScope j⟩
    exact scoped_sum3 _ _ (fun k=>⟨directionScope k,directionScope k⟩)
  have selectedScope (j : Fin 3) (plus : Bool) : (selected row j plus).Scoped 1200:=by
    change True ∧ neighborRegister row j plus<1200
    refine ⟨trivial,?_⟩
    unfold neighborRegister
    split_ifs <;> omega
  exact ⟨⟨scoped_sum3 _ _ (fun j=>⟨blockScope j,trivial⟩),trivial⟩,
    trivial,scoped_sum3 _ _ (fun j=>⟨trivial,selectedScope j true,selectedScope j false⟩)⟩

theorem noncentral_right (f : Alias→Fin 3→ℚ) :
    rationalNoncentral (rationalRightCoupling f)=rationalRightCoupling f := by
  funext ν j
  unfold rationalNoncentral rationalRightCoupling
  by_cases h:rationalCentralCheck ν
  · simp only [rationalNoncentral,h,↓reduceIte,Pi.smul_apply,smul_eq_mul,mul_zero]
  · simp only [h,Bool.false_eq_true,↓reduceIte]

theorem cached_value (row column : Fin 24) (N : ℕ) (v : ℕ→ℚ)
    (read : ∀j plus,v (neighborRegister row j plus)=
      extendAliasArray (N+3)
        (cachedInverseApply (v 232) (v 233) (fun k=>v (234+k.val)) (N+3)
          (rationalRightCoupling (rationalBasisField column)) (N+1))
        (neighbor row j plus) (polarization row)) :
    (expression row column).evaluate v=
      cachedSchurMatrix (v 232) (v 233) (fun k=>v (234+k.val)) (N+1) row column := by
  rw [value row column v _ read]
  simp only [cachedSchurMatrix,cachedSchurApply,noncentral_right,Pi.sub_apply,
    corner,polarization]

#print axioms value
end Maxwell.Continuum.Calibration.SchurExpression
