import Maxwell.Cost.CalibrationMatrix.Horner.PairingEmit

namespace Maxwell.Cost.CalibrationMatrix.Horner

def PairingRow.Separated {n : ℕ} (r : PairingRow n) (d : Data n) : Prop :=
  (∀ i, IncidenceEncoding.Separated (addressValue r.positiveBase) (n*addressValue d.width)
    (addressValue (d.bases i)) (n*addressValue d.width)) ∧
  (∀ i, IncidenceEncoding.Separated (addressValue r.negativeBase) (n*addressValue d.width)
    (addressValue (d.bases i)) (n*addressValue d.width))

theorem represents_of_horner_outside {n m base width : ℕ} {d : Data n} {s t : BitRAMState}
    {words : Vector (List Bool) m} (hr : BitArray.Represents s.memory base width words)
    (hout : Outside d s t)
    (hsep : ∀ i, IncidenceEncoding.Separated base (m*width)
      (addressValue (d.bases i)) (n*addressValue d.width)) : BitArray.Represents t.memory base width words := by
  refine ⟨hr.length,?_⟩
  intro i j hj
  rw [hout]
  · exact hr.bits i j hj
  · intro k
    have hs := Nat.mul_le_mul_right width (show i.val+1 ≤ m by omega)
    rcases hsep k with hp | hp
    · left;nlinarith
    · right;omega

theorem FinishFrame.high {s t : BitRAMState} (h : FinishFrame s t) (i : ℕ) (hi : 141 ≤ i) :
    t.tapes i = s.tapes i := by
  apply h.2.2.2.1 i (Or.inr (by omega)) (Or.inr (by omega)) _ (by omega)
  simp only [mutableTapes,List.mem_cons,List.not_mem_nil,or_false,not_or]
  omega

theorem FinishFrame.matrix_base {s t : BitRAMState} (h : FinishFrame s t) (i : ℕ)
    (hi : i = 110 ∨ i = 111) : t.tapes i = s.tapes i := by
  rcases hi with rfl | rfl <;> apply h.2.2.2.1 <;> simp [mutableTapes]

theorem PairingRow.Stored.after_inverse {n : ℕ} {r : PairingRow n} {d : Data n}
    {s t : BitRAMState} (hr : r.Stored (addressValue d.width) s) (hf : FinishFrame s t)
    (hout : Outside d s t) (hsep : r.Separated d) : r.Stored (addressValue d.width) t :=
  ⟨BankArray.word_of_eq (hf.high 154 (by omega)) hr.positiveBase,
    BankArray.word_of_eq (hf.high 155 (by omega)) hr.negativeBase,
    represents_of_horner_outside hr.positive hout hsep.1,
    represents_of_horner_outside hr.negative hout hsep.2⟩

theorem PairingRow.Stored.after_denominator {n : ℕ} {r : PairingRow n} {width : ℕ}
    {s t : BitRAMState} (hr : r.Stored width s) (hf : Denominator.Frame s t) : r.Stored width t :=
  ⟨BankArray.word_of_eq (hf.2.2.2.2.2.1 154 (by omega) (Or.inr (by omega)) (by omega) (by omega)) hr.positiveBase,
    BankArray.word_of_eq (hf.2.2.2.2.2.1 155 (by omega) (Or.inr (by omega)) (by omega) (by omega)) hr.negativeBase,
    by simpa only [hf.2.2.1] using hr.positive,by simpa only [hf.2.2.1] using hr.negative⟩

def pairingOld {n : ℕ} (a : Snapshot n) (N : ℕ) : PairingOld :=
  ⟨a.data.matrixPositiveBase,a.data.matrixNegativeBase,(a.iterate N).data.bases 10,(a.iterate N).data.bases 11⟩

theorem pairingOld_stored {n : ℕ} {a : Snapshot n} {N : ℕ} {s t : BitRAMState}
    (hs : Stored a.data a.words s) (hp : Ports (a.iterate N).data 10 11 2 3 t) (hf : FinishFrame s t) :
    (pairingOld a N).Stored t :=
  ⟨BankArray.word_of_eq (hf.matrix_base 110 (Or.inl rfl)) hs.matrixPositiveBase,
    BankArray.word_of_eq (hf.matrix_base 111 (Or.inr rfl)) hs.matrixNegativeBase,hp.inputPositive,hp.inputNegative⟩

theorem PairingOld.Stored.after_denominator {old : PairingOld} {s t : BitRAMState}
    (h : old.Stored s) (hf : Denominator.Frame s t) : old.Stored t :=
  ⟨BankArray.word_of_eq (hf.keep_work 110 (by omega) (Or.inr (by omega)) (by omega)) h.1,
    BankArray.word_of_eq (hf.keep_work 111 (by omega) (Or.inr (by omega)) (by omega)) h.2.1,
    BankArray.word_of_eq (hf.keep_work 112 (by omega) (Or.inr (by omega)) (by omega)) h.2.2.1,
    BankArray.word_of_eq (hf.keep_work 113 (by omega) (Or.inr (by omega)) (by omega)) h.2.2.2⟩

end Maxwell.Cost.CalibrationMatrix.Horner
