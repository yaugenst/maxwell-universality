import Maxwell.Continuum.RationalDataflowMatrixVector
import Maxwell.Continuum.RationalDataflowExpressionVectorBounds
import Maxwell.Continuum.CalibrationRationalCoordinates

/-! The central calibration inverse acts on24 stored rational coordinates.
The implementation and execution proof are the dimension-generic rational
matrix/vector compiler; this file only selects its register layout. -/
namespace Maxwell.Continuum.Calibration.CentralMatvec
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow MatrixVector
set_option maxHeartbeats 2200000
set_option maxRecDepth 16384

def layout : Layout 24 := ⟨1700,2400,2424,2448,by decide,by decide,by decide⟩
def bank : Finset ℕ := layout.bank
def code : Code := layout.code
def values (v : ℕ→Parts) : ℕ→Parts := layout.values v
def width (B : ℕ) : ℕ := layout.width B
def cost (B : ℕ) : ℕ := layout.cost B
def runtimeCoefficient : ℕ := ExpressionVector.costCoefficient layout.expression (List.finRange 24)
def wordCoefficient : ℕ := ExpressionVector.widthCoefficient layout.expression (List.finRange 24)

theorem cost_quadratic (B : ℕ) : cost B≤runtimeCoefficient*(B+3)^2 :=
  ExpressionVector.cost_quadratic layout.expression (List.finRange 24) B

theorem width_linear (B : ℕ) : width B+1≤wordCoefficient*(B+1) :=
  ExpressionVector.resultWidth_linear layout.expression (List.finRange 24) B

theorem executes (v : ℕ→Parts) (B : ℕ) (positive : 1≤B)
    (bounded : WidthBank bank B v) (good : Good bank v)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (ready : Ready bank v s) :
    ∃steps t,Executes input tape code steps s t ∧ steps≤cost B ∧
      Ready bank (values v) t ∧ Good bank (values v) ∧ WidthBank bank (width B) (values v) ∧
      (∀r : Fin 24,(values v (2424+r.val)).value=
        ∑j : Fin 24,(v (1700+24*r.val+j.val)).value*(v (2400+j.val)).value) ∧
      BinaryPrecision.Frame (workspace bank) s.val t.val := by
  exact layout.executes v B positive bounded good input tape s ready

theorem values_retained (v : ℕ→Parts) (i : ℕ) (below : i<2424) : values v i=v i :=
  layout.values_keep v i below

theorem expanded_result (v : ℕ→Parts) (M : Matrix (Fin 24) (Fin 24) ℚ)
    (f : FreeFiber.Alias→Fin 3→ℚ)
    (matrix : ∀i j,(v (1700+24*i.val+j.val)).value=M i j)
    (vector : ∀j : Fin 24,(v (2400+j.val)).value=rationalCoordinates f j)
    (result : ∀i : Fin 24,(values v (2424+i.val)).value=
      ∑j : Fin 24,(v (1700+24*i.val+j.val)).value*(v (2400+j.val)).value) :
    rationalExpandCoordinates (fun i : Fin 24=>(values v (2424+i.val)).value)=rationalCentralMatrixApply M f := by
  apply congrArg rationalExpandCoordinates
  funext i
  rw [result i]
  apply Finset.sum_congr rfl
  intro j _
  rw [matrix i j,vector j]
  rfl

#print axioms executes
#print axioms expanded_result
end Maxwell.Continuum.Calibration.CentralMatvec
