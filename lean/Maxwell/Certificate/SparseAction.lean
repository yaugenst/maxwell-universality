import Maxwell.Certificate.PrimitiveBinding

namespace Maxwell.Certificate.PrimitiveBinding
open Maxwell.Spectral Maxwell.Spectral.PrimitiveYee
open Maxwell.Spectral.PeriodicYee (Direction)
open Matrix
noncomputable section

def phaseQ (k : Translation) (j : Direction) (p : Cell) : ℚ :=
  (-1 : ℚ) ^ (∑ a, k a * reduceTranslation (forwardRaw j p) a)

def differenceActionQ (k : Translation) (j : Direction) (v : Cell → ℚ) (p : Cell) : ℚ :=
  phaseQ k j p * v (forwardCell j p) - v p

def differenceTransposeActionQ (k : Translation) (j : Direction) (v : Cell → ℚ) (p : Cell) : ℚ :=
  phaseQ k j (backwardCell j p) * v (backwardCell j p) - v p

theorem differenceActionQ_correct (k : Translation) (j : Direction) (v : Cell → ℚ) (p : Cell) :
    (differenceQ k j *ᵥ v) p = differenceActionQ k j v p := by
  simp [differenceQ, differenceActionQ, phaseQ, Matrix.mulVec, dotProduct, sub_mul,
    Finset.sum_sub_distrib, ite_mul]

theorem differenceTransposeActionQ_correct (k : Translation) (j : Direction)
    (v : Cell → ℚ) (p : Cell) :
    ((differenceQ k j).transpose *ᵥ v) p = differenceTransposeActionQ k j v p := by
  have he (q : Cell) : p = forwardCell j q ↔ q = backwardCell j p := by
    constructor
    · intro h
      rw [h, backward_forward]
    · rintro rfl
      exact (forward_backward j p).symm
  simp [differenceQ, differenceTransposeActionQ, phaseQ, Matrix.mulVec, dotProduct,
    Matrix.transpose_apply, sub_mul, Finset.sum_sub_distrib, ite_mul, he]

def curlActionQ (k : Translation) (v : Electric → ℚ) (e : Electric) : ℚ :=
  if e.1 = 0 then
    differenceActionQ k 1 (fun p => v (2,p)) e.2 - differenceActionQ k 2 (fun p => v (1,p)) e.2
  else if e.1 = 1 then
    differenceActionQ k 2 (fun p => v (0,p)) e.2 - differenceActionQ k 0 (fun p => v (2,p)) e.2
  else
    differenceActionQ k 0 (fun p => v (1,p)) e.2 - differenceActionQ k 1 (fun p => v (0,p)) e.2

def curlTransposeActionQ (k : Translation) (v : Face → ℚ) (e : Electric) : ℚ :=
  if e.1 = 0 then
    differenceTransposeActionQ k 2 (fun p => v (1,p)) e.2 -
      differenceTransposeActionQ k 1 (fun p => v (2,p)) e.2
  else if e.1 = 1 then
    differenceTransposeActionQ k 0 (fun p => v (2,p)) e.2 -
      differenceTransposeActionQ k 2 (fun p => v (0,p)) e.2
  else
    differenceTransposeActionQ k 1 (fun p => v (0,p)) e.2 -
      differenceTransposeActionQ k 0 (fun p => v (1,p)) e.2

theorem curlActionQ_correct (k : Translation) (v : Electric → ℚ) (e : Electric) :
    (curlQ k *ᵥ v) e = curlActionQ k v e := by
  rcases e with ⟨a,p⟩
  simp only [Matrix.mulVec, dotProduct]
  rw [Fintype.sum_prod_type, Fin.sum_univ_three]
  fin_cases a <;>
    simp [curlActionQ, curlQ, ← differenceActionQ_correct, Matrix.mulVec, dotProduct,
      neg_mul, Finset.sum_neg_distrib] <;> ring

theorem curlTransposeActionQ_correct (k : Translation) (v : Face → ℚ) (e : Electric) :
    ((curlQ k).transpose *ᵥ v) e = curlTransposeActionQ k v e := by
  rcases e with ⟨a,p⟩
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  rw [Fintype.sum_prod_type, Fin.sum_univ_three]
  fin_cases a <;>
    simp [curlTransposeActionQ, curlQ, ← differenceTransposeActionQ_correct,
      Matrix.mulVec, dotProduct, Matrix.transpose_apply, neg_mul, Finset.sum_neg_distrib] <;> ring

def fiberActionQ (k : Translation) (v : Electric → ℚ) (e : Electric) : ℚ :=
  curlTransposeActionQ k (curlActionQ k v) e - edgeAverageQ e / 64 * v e

theorem fiberActionQ_correct (k : Translation) (v : Electric → ℚ) (e : Electric) :
    (fiberQ k *ᵥ v) e = fiberActionQ k v e := by
  have hc : curlQ k *ᵥ v = curlActionQ k v := funext (curlActionQ_correct k v)
  simp only [fiberQ, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, Matrix.smul_mulVec, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul, hc]
  rw [curlTransposeActionQ_correct]
  simp [fiberActionQ, massQ, Matrix.mulVec_diagonal]
  ring

end
end Maxwell.Certificate.PrimitiveBinding
