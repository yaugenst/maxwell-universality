import Maxwell.Certificate.IntervalMatrix
import Mathlib.LinearAlgebra.Matrix.Notation

/-! An actual 2-by-2 interval matrix from the first canonical global record.
The record uses `6144_10240_2048_4.npz`, center `(3/32,5/32,1/32)`, and
negative-field norm bound `8.484232529066503`. The producer forms
`bound^2 / 128 * I - Gram(field_negative) / 128` in 48-bit intervals.

These literals are proposals. Lean independently accepts their Schur
certificate. Binding the enclosed matrix to the Fourier-field expression
requires the corresponding entry-containment proofs and is a separate step. -/

namespace Maxwell.Certificate.IntervalMatrix

open scoped ComplexOrder

def sourceRectangle48 (re im : ℤ) (radius : ℕ) : ComplexRectangle :=
  ⟨⟨re / (2 : ℚ)^48, radius / (2 : ℚ)^48, by positivity⟩,
   ⟨im / (2 : ℚ)^48, radius / (2 : ℚ)^48, by positivity⟩⟩

def firstNegativeNormGram : Enclosure 2 :=
  !![sourceRectangle48 11953246751115 0 38,
      sourceRectangle48 (-3069714) (-20558) 68;
     sourceRectangle48 (-3069714) 20558 68,
      sourceRectangle48 11942166480634 0 111]

/-- A deliberately short rational enclosure of the single Schur entry. -/
def firstNegativeNormSchur : Enclosure 1 := fun _ _ =>
  ⟨⟨1 / 20, 1 / 50, by norm_num⟩, ⟨0, 1 / 50, by norm_num⟩⟩

def firstNegativeNormProposal : Proposal 2 :=
  .next firstNegativeNormSchur (.next (fun i => Fin.elim0 i) .empty)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem firstNegativeNormGram_accepted :
    accepts firstNegativeNormGram firstNegativeNormProposal = true := by
  decide +kernel

theorem firstNegativeNormGram_sound {A : Matrix (Fin 2) (Fin 2) ℂ}
    (hA : A.IsHermitian) (ha : Contains firstNegativeNormGram A) : A.PosSemidef :=
  accepts_sound firstNegativeNormProposal firstNegativeNormGram_accepted hA ha

end Maxwell.Certificate.IntervalMatrix
