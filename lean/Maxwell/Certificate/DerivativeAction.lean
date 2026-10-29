import Maxwell.Certificate.DerivativeBinding
import Maxwell.Certificate.DerivativeInteger

namespace Maxwell.Certificate.DerivativeBinding
open Maxwell.Spectral Maxwell.Spectral.PrimitiveYee
open Maxwell.Spectral.PeriodicYee (Direction)
open Maxwell.Certificate.PrimitiveBinding
open Matrix
noncomputable section

theorem curlBlockQ_mulVec (D : Direction → Matrix Cell Cell ℚ) (v : Electric → ℚ)
    (e : Electric) :
    (curlBlockQ D *ᵥ v) e = blockAction (fun j v p => (D j *ᵥ v) p) v e := by
  rcases e with ⟨a,p⟩
  simp only [Matrix.mulVec, dotProduct]
  rw [Fintype.sum_prod_type, Fin.sum_univ_three]
  fin_cases a <;>
    simp [curlBlockQ, blockAction, neg_mul, Finset.sum_neg_distrib] <;> ring

theorem curlBlockQ_transpose_mulVec (D : Direction → Matrix Cell Cell ℚ)
    (v : Electric → ℚ) (e : Electric) :
    ((curlBlockQ D).transpose *ᵥ v) e =
      blockTransposeAction (fun j v p => ((D j).transpose *ᵥ v) p) v e := by
  rcases e with ⟨a,p⟩
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  rw [Fintype.sum_prod_type, Fin.sum_univ_three]
  fin_cases a <;>
    simp [curlBlockQ, blockTransposeAction, neg_mul, Finset.sum_neg_distrib] <;> ring

theorem firstActionI_cast (k : Translation) (j : Direction) (v : Cell → ℤ)
    (d : ℚ) (p : Cell) :
    ((differenceQ k j + (2:ℚ) • 1) *ᵥ (fun p => (v p : ℚ) / d)) p =
      (firstActionI k j v p : ℚ) / d := by
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, differenceActionQ_correct, differenceActionI_cast,
    firstActionI, Int.cast_add, Int.cast_mul, Int.cast_ofNat]
  ring

theorem firstTransposeActionI_cast (k : Translation) (j : Direction) (v : Cell → ℤ)
    (d : ℚ) (p : Cell) :
    ((differenceQ k j + (2:ℚ) • 1).transpose *ᵥ (fun p => (v p : ℚ) / d)) p =
      (firstTransposeActionI k j v p : ℚ) / d := by
  simp only [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one,
    Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, differenceTransposeActionQ_correct,
    differenceTransposeActionI_cast, firstTransposeActionI, Int.cast_add,
    Int.cast_mul, Int.cast_ofNat]
  ring

theorem KActionI_cast (k : Translation) (i : Direction) (v : Electric → ℤ)
    (d : ℚ) (e : Electric) :
    (KQ k i *ᵥ (fun e => (v e : ℚ) / d)) e = (KActionI k i v e : ℚ) / d := by
  rw [KQ, curlBlockQ_mulVec]
  rcases e with ⟨a,p⟩
  fin_cases i <;> fin_cases a <;>
    simp [blockAction, KActionI, firstActionI_cast] <;> ring

theorem KTransposeActionI_cast (k : Translation) (i : Direction) (v : Electric → ℤ)
    (d : ℚ) (e : Electric) :
    ((KQ k i).transpose *ᵥ (fun e => (v e : ℚ) / d)) e =
      (KTransposeActionI k i v e : ℚ) / d := by
  rw [KQ, curlBlockQ_transpose_mulVec]
  rcases e with ⟨a,p⟩
  fin_cases i <;> fin_cases a <;>
    simp [blockTransposeAction, KTransposeActionI, firstTransposeActionI_cast,
      -Matrix.transpose_add, -Matrix.transpose_smul, -Matrix.transpose_one] <;> ring

theorem LActionI_cast (k : Translation) (i : Direction) (v : Electric → ℤ)
    (d : ℚ) (e : Electric) :
    (LQ k i *ᵥ (fun e => (v e : ℚ) / d)) e = (LActionI k i v e : ℚ) / d := by
  rw [LQ, curlBlockQ_mulVec]
  rcases e with ⟨a,p⟩
  fin_cases i <;> fin_cases a <;>
    simp [blockAction, LActionI, differenceActionQ_correct,
      differenceActionI_cast] <;> ring

theorem LTransposeActionI_cast (k : Translation) (i : Direction) (v : Electric → ℤ)
    (d : ℚ) (e : Electric) :
    ((LQ k i).transpose *ᵥ (fun e => (v e : ℚ) / d)) e =
      (LTransposeActionI k i v e : ℚ) / d := by
  rw [LQ, curlBlockQ_transpose_mulVec]
  rcases e with ⟨a,p⟩
  fin_cases i <;> fin_cases a <;>
    simp [blockTransposeAction, LTransposeActionI, differenceTransposeActionQ_correct,
      differenceTransposeActionI_cast] <;> ring


theorem curlQI_cast (k : Translation) (v : Electric → ℤ) (d : ℚ) :
    curlQ k *ᵥ (fun e => (v e : ℚ) / d) = fun e => (curlActionI k v e : ℚ) / d := by
  funext e
  rw [curlActionQ_correct, curlActionI_cast]

theorem curlTransposeQI_cast (k : Translation) (v : Electric → ℤ) (d : ℚ)
    (e : Electric) :
    ((curlQ k).transpose *ᵥ (fun e => (v e : ℚ) / d)) e =
      (curlTransposeActionI k v e : ℚ) / d := by
  rw [curlTransposeActionQ_correct, curlTransposeActionI_cast]

theorem BActionI_cast (k : Translation) (i : Direction) (v : Electric → ℤ)
    (d : ℚ) (e : Electric) :
    (BQ k i *ᵥ (fun e => (v e : ℚ) / d)) e = (BActionI k i v e : ℚ) / d := by
  have hk : KQ k i *ᵥ (fun e => (v e : ℚ) / d) =
      fun e => (KActionI k i v e : ℚ) / d := funext (KActionI_cast k i v d)
  simp only [BQ, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, hk, curlQI_cast,
    Pi.sub_apply, curlTransposeQI_cast, KTransposeActionI_cast, BActionI, Int.cast_sub]
  ring

theorem DActionI_cast (k : Translation) (i j : Direction) (v : Electric → ℤ)
    (d : ℚ) (e : Electric) :
    (DQ k i j *ᵥ (fun e => (v e : ℚ) / d)) e = (DActionI k i j v e : ℚ) / d := by
  have hk (a : Direction) : KQ k a *ᵥ (fun e => (v e : ℚ) / d) =
      fun e => (KActionI k a v e : ℚ) / d := funext (KActionI_cast k a v d)
  have hl (a : Direction) : LQ k a *ᵥ (fun e => (v e : ℚ) / d) =
      fun e => (LActionI k a v e : ℚ) / d := funext (LActionI_cast k a v d)
  by_cases hij : i = j
  · simp only [DQ, DActionI, hij, ↓reduceIte, Matrix.sub_mulVec, Matrix.add_mulVec,
      ← Matrix.mulVec_mulVec, hk, hl, curlQI_cast, Pi.sub_apply, Pi.add_apply,
      KTransposeActionI_cast, LTransposeActionI_cast, curlTransposeQI_cast,
      Int.cast_add, Int.cast_sub]
    ring
  · simp only [DQ, DActionI, hij, ↓reduceIte, sub_zero, Matrix.add_mulVec,
      ← Matrix.mulVec_mulVec, hk, Pi.add_apply, KTransposeActionI_cast, Int.cast_add]
    ring

end
end Maxwell.Certificate.DerivativeBinding
