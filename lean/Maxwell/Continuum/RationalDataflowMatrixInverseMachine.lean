import Maxwell.Continuum.RationalDataflowMatrixInversePlan

/-! Actual execution of the complete adjugate/determinant inverse. Matrix
dimension is fixed by the program; cost is quadratic in input word width.
Singular matrices follow the total rational inverse convention. -/
namespace Maxwell.Continuum.RationalDataflow.MatrixInverse
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

def width (n B : ℕ) : ℕ := 2^(steps n)*(B+1)
def cost (n B : ℕ) : ℕ := steps n*operationCost (width n B)+1
def costCoefficient (n : ℕ) : ℕ := steps n*2^100*(2^(steps n)+3)^2+1

theorem control_steps (n : ℕ) : (control n).steps≤steps n := by
  simpa only [control,coordinates,List.length_ofFn,steps] using traversal_steps n (coordinates n)

theorem cost_polynomial (n B : ℕ) : cost n B≤costCoefficient n*(B+1)^2 := by
  have argument : width n B+3≤(2^(steps n)+3)*(B+1) := by unfold width;nlinarith
  have square := Nat.pow_le_pow_left argument 2
  have one : 1≤(B+1)^2 := one_le_pow₀ (by omega)
  unfold cost operationCost costCoefficient
  calc
    _≤steps n*(2^100*((2^(steps n)+3)*(B+1))^2)+1 := by gcongr
    _≤(steps n*2^100*(2^(steps n)+3)^2+1)*(B+1)^2 := by
      rw [mul_pow]
      nlinarith only [one]

theorem executes (n B : ℕ) (hB : 1≤B) (v : ℕ→Parts)
    (hw : WidthBank (registers n) B v) (hg : Good (registers n) v)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : Ready (registers n) v s) :
    ∃used t out,Executes input tape (control n).code used s t ∧ used≤cost n B ∧
      Ready (registers n) out t ∧ Good (registers n) out ∧ WidthBank (registers n) (width n B) out ∧
      (∀i j,(out (output n i j)).value=
        (source n (valueBank v)).det⁻¹*(source n (valueBank v)).adjugate i j) ∧
      source n (valueBank out)=source n (valueBank v) ∧
      BinaryPrecision.Frame (workspace (registers n)) s.val t.val := by
  have valid := traversal_valid n (coordinates n)
  have admissible := traversal_admissible n (coordinates n) v hg
  have trace := (control n).automatic_widthTrace (registers n) valid v B hw
    (traversal_literals n (coordinates n) B hB)
  have trace' := trace.mono (Nat.mul_le_mul_right (B+1)
    (Nat.pow_le_pow_right (by decide) (control_steps n)))
  obtain ⟨c,t,e,hc,b,f⟩ := (control n).executes (registers n) valid v (width n B) trace'
    hg admissible input tape s hs
  have values := (control n).evaluate_value (registers n) valid v hg admissible
  have result := traversal_result n (coordinates n) (valueBank v)
  refine ⟨c,t,(control n).evaluate v,e,
    hc.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ (control_steps n)) 1),b,
    (control n).evaluate_good (registers n) valid v hg admissible,trace'.result,?_,?_,f⟩
  · intro i j
    exact (congrFun values (output n i j)).trans (result.2.1 (i,j) (coordinates_complete n i j))
  · rw [values]
    exact result.1

#print axioms executes
#print axioms cost_polynomial
end Maxwell.Continuum.RationalDataflow.MatrixInverse
