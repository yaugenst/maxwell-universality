import Maxwell.Continuum.RationalDataflowMatrixInverseMachine
import Maxwell.Continuum.CalibrationRationalInverse

/-! The fixed 24-by-24 central inverse is computed by literal arithmetic,
including the singular branch of the existing rational definition. -/
namespace Maxwell.Continuum.Calibration.CentralMatrixMachine
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384
attribute [local irreducible] MatrixInverse.control MatrixInverse.registers MatrixInverse.width
  MatrixInverse.cost MatrixInverse.costCoefficient

def code : Code := (MatrixInverse.control 24).code

theorem executes (B : ℕ) (hB : 1≤B) (v : ℕ→Parts)
    (hw : WidthBank (MatrixInverse.registers 24) B v) (hg : Good (MatrixInverse.registers 24) v)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : Ready (MatrixInverse.registers 24) v s) :
    ∃used t out,Executes input tape code used s t ∧ used≤MatrixInverse.costCoefficient 24*(B+1)^2 ∧
      Ready (MatrixInverse.registers 24) out t ∧ Good (MatrixInverse.registers 24) out ∧
      WidthBank (MatrixInverse.registers 24) (MatrixInverse.width 24 B) out ∧
      (∀i j,(out (MatrixInverse.output 24 i j)).value=
        rationalMatrixInverse (MatrixInverse.source 24 (valueBank v)) i j) ∧
      MatrixInverse.source 24 (valueBank out)=MatrixInverse.source 24 (valueBank v) ∧
      BinaryPrecision.Frame (workspace (MatrixInverse.registers 24)) s.val t.val := by
  obtain ⟨c,t,out,e,hc,ready,good,width,value,source,frame⟩ := MatrixInverse.executes 24 B hB v hw hg
    input tape s hs
  exact ⟨c,t,out,e,hc.trans (MatrixInverse.cost_polynomial 24 B),ready,good,width,
    fun i j => value i j,source,frame⟩

#print axioms executes
end Maxwell.Continuum.Calibration.CentralMatrixMachine
