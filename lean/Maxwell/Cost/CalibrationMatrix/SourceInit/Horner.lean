import Maxwell.Cost.CalibrationMatrix.SourceInit.Execute
import Maxwell.Cost.CalibrationMatrix.Horner.Store

namespace Maxwell.Cost.CalibrationMatrix.SourceInit

theorem represents_of_outside {m n size width base : ℕ} {d : Data m n}
    {words : Vector (List Bool) size} {s t : BitRAMState}
    (h : BitArray.Represents s.memory base width words) (hm : Outside d s t)
    (hsep : ∀ port, IncidenceEncoding.Separated base (size*width)
      (addressValue (d.outputBases port)) (n*addressValue d.width)) :
    BitArray.Represents t.memory base width words := by
  refine ⟨h.length, ?_⟩
  intro i j hj
  rw [hm]
  · exact h.bits i j hj
  · intro port
    have hs := Nat.mul_le_mul_right width (show i.val+1 ≤ size by omega)
    rcases hsep port with hp | hp
    · left; nlinarith
    · right; omega

def hornerWords {n : ℕ} (initial : Fin 12 → Vector (List Bool) n)
    (source : Fin 4 → Vector (List Bool) n) : Fin 12 → Vector (List Bool) n :=
  fun i => if h : i.val < 4 then source ⟨i.val, h⟩ else initial i

/-- The physical initializer's result installs both initial Horner vectors
while retaining the matrix and all eight remaining workspace arrays. -/
theorem horner_stored {m n : ℕ} (d : Data m n) (h : Horner.Data n)
    (hwidth : d.width = h.width)
    (hbases : ∀ i : Fin 4, d.outputBases i = h.bases ⟨i.val, by omega⟩)
    (initial : Fin 12 → Vector (List Bool) n) (source : Fin 4 → Vector (List Bool) n)
    (s t : BitRAMState) (hs : Horner.Stored h initial s) (ht : Stored d source t)
    (hf : MatrixFrame s t) (hout : Outside d s t) :
    Horner.Stored h (hornerWords initial source) t := by
  have keep (i : ℕ) (hi : Horner.Metadata i) : t.tapes i = s.tapes i := by
    apply hf.2.2.2.1 i <;> simp only [Horner.Metadata] at hi <;> omega
  refine ⟨BankArray.word_of_eq (keep 100 (by simp [Horner.Metadata])) hs.width,
    BankArray.word_of_eq (keep 101 (by simp [Horner.Metadata])) hs.clock,
    BankArray.word_of_eq (keep 110 (by simp [Horner.Metadata])) hs.matrixPositiveBase,
    BankArray.word_of_eq (keep 111 (by simp [Horner.Metadata])) hs.matrixNegativeBase,
    fun i => BankArray.word_of_eq (keep _ (by
      right; right; right; right; exact Horner.baseBank_bounds i)) (hs.bases i),
    RationalAccumulator.word_of_eq (keep 126 (by simp [Horner.Metadata])) hs.K,
    RationalAccumulator.word_of_eq (keep 127 (by simp [Horner.Metadata])) hs.S,
    represents_of_outside hs.matrixPositive hout (fun i => by
      rw [hbases, hwidth]; exact h.matrixPositive_separated _),
    represents_of_outside hs.matrixNegative hout (fun i => by
      rw [hbases, hwidth]; exact h.matrixNegative_separated _), ?_⟩
  intro i
  by_cases hi : i.val < 4
  · simp only [hornerWords, hi, dite_true]
    have hc := ht.outputs ⟨i.val, hi⟩
    simpa only [hbases, hwidth] using hc
  · simp only [hornerWords, hi, dite_false]
    exact represents_of_outside (hs.arrays i) hout (fun j => by
      rw [hbases, hwidth]
      apply h.separated i
      intro he
      have heq := congrArg Fin.val he
      change i.val = j.val at heq
      have hj := j.isLt
      omega)

end Maxwell.Cost.CalibrationMatrix.SourceInit
