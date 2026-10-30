import Maxwell.Continuum.FourierTensorMachineTerm
import Maxwell.Continuum.RationalDataflowRegisterWidths

/-! The tensor accumulator grows additively in the number of Fourier
aliases. Cached inputs are never multiplied by the accumulated sum. -/

namespace Maxwell.Continuum.Profile.TensorMachine
open RationalDataflow
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

def registerBounds (B W : ℕ) (i : ℕ) : ℕ := if 1 ≤ i ∧ i≤8 then W else B

theorem instructions_width (B W : ℕ) :
    programWidth instructions (registerBounds B W)≤B+22*W+22 := by
  simp [programWidth,instructions,Instruction.resultWidth,Instruction.widthUpdate,
    registerBounds]
  omega

private theorem trace_result {S : Finset ℕ} {B : ℕ} (ins : List Instruction) (v : ℕ→Parts)
    (h : WidthTrace S B ins v) : WidthBank S B (RationalDataflow.evaluate ins v) := by
  induction ins generalizing v with
  | nil => exact h
  | cons a rest ih => exact ih (a.update v) h.2.2

theorem body_widthTrace (v : ℕ→Parts) (B W : ℕ) (hv : WidthBank ids B v)
    (hi : ∀i,1 ≤ i → i≤8 → (v i).Width W) : body.WidthTrace ids (B+22*W+22) v := by
  have hvar : RegisterWidths ids (registerBounds B W) v := by
    intro i him
    by_cases hx : 1 ≤ i ∧ i≤8
    · simpa only [registerBounds, ite_eq_left hx] using hi i hx.1 hx.2
    · simpa only [registerBounds, ite_eq_right hx] using hv i him
  have hvalid : ∀a∈instructions,a.Valid ids := by
    simp [instructions,Instruction.Valid,ids]
  have ht := inferred_widthTrace ids instructions hvalid (registerBounds B W) v hvar
    (B+22*W+22) (hv.mono (by omega)) (instructions_width B W)
  exact Control.prepend_widthTrace ids instructions Control.done v (B+22*W+22) ht
    (trace_result instructions v ht)

theorem body_output_width (v : ℕ→Parts) (B W : ℕ) (hv : WidthBank ids B v)
    (hi : ∀i,1 ≤ i → i≤8 → (v i).Width W) : WidthBank ids (B+22*W+22) (body.evaluate v) :=
  (body_widthTrace v B W hv hi).result

#print axioms body_widthTrace
#print axioms body_output_width
end Maxwell.Continuum.Profile.TensorMachine
