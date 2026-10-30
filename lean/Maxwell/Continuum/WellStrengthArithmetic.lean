import Maxwell.Continuum.NearestIntegerExecution
import Maxwell.Continuum.FiniteAuxiliaryDyadicBits

/-! Exact finite reciprocal tuning from the stored calibrated midpoint
and target diagonal. The result is the paper's half-up dyadic numerator. -/
namespace Maxwell.Continuum.RationalDataflow.WellStrength
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 2500000

def bank : Finset ℕ := Finset.range 16

def reciprocal : Control :=
  .step (.binary .add 3 1 2) (.step (.inverse 3 3) .done)

def prepared (v : ℕ→Parts) : ℕ→Parts := reciprocal.evaluate v

def values (P : ℕ) (v : ℕ→Parts) : ℕ→Parts :=
  NearestInteger.values P 0 3 (prepared v)

def numerator (P : ℕ) (μ θ : ℚ) : ℤ :=
  (Maxwell.Logical.Rounding.nearest P (μ+θ)⁻¹).numerator

theorem reciprocal_valid : reciprocal.Valid bank := by
  simp [reciprocal,Control.Valid,Instruction.Valid,bank]

theorem reciprocal_fits (W : ℕ) : reciprocal.LiteralsFit W := by trivial

theorem prepared_three (v : ℕ→Parts) :
    prepared v 3=((v 1).add (v 2)).inverse := by
  simp [prepared,reciprocal,Control.evaluate,Instruction.update,BinaryOp.eval]

theorem reciprocal_admissible (v : ℕ→Parts) (hg : Good bank v)
    (hn : (v 1).value+(v 2).value≠0) : reciprocal.AdmissibleTrace v := by
  refine ⟨trivial,?_,trivial⟩
  change ((v 1).add (v 2)).value≠0
  rwa [Parts.add_value _ _ (hg 1 (by decide)) (hg 2 (by decide))]

theorem prepared_value (v : ℕ→Parts) (hg : Good bank v)
    (hn : (v 1).value+(v 2).value≠0) :
    (prepared v 3).value=((v 1).value+(v 2).value)⁻¹ := by
  have h1 := hg 1 (by decide)
  have h2 := hg 2 (by decide)
  rw [prepared_three,Parts.inverse_value _ (Parts.add_valid h1 h2)
    (by rwa [Parts.add_value _ _ h1 h2]),Parts.add_value _ _ h1 h2]

theorem values_zero (P : ℕ) (v : ℕ→Parts) (hg : Good bank v)
    (hn : (v 1).value+(v 2).value≠0) :
    values P v 0=Parts.literal (numerator P (v 1).value (v 2).value : ℚ) := by
  simp only [values,NearestInteger.values,Function.update_self,NearestInteger.result,
    prepared_value v hg hn,numerator]

theorem onsite_numerator (L d : ℕ) (hL : 0<L) (I : Calibration.RationalInterval) (θ : ℚ) :
    numerator (FiniteAuxiliary.onsitePrecision L d hL) I.midpoint θ=
      (FiniteAuxiliary.onsiteRound L hL (Parameters.zeta d) (Parameters.zeta_pos d) I θ).numerator := rfl

#print axioms values_zero
#print axioms onsite_numerator
end Maxwell.Continuum.RationalDataflow.WellStrength
