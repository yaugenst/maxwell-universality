import Maxwell.Cost.CalibrationMatrix.LoadTerm

namespace Maxwell.Cost.CalibrationMatrix

open Structured

def Data.Sized {m n : ℕ} (d : Data m n) (B : ℕ) : Prop :=
  d.width.length ≤ B ∧ addressValue d.width ≤ B ∧
  d.matrixPositiveBase.length ≤ B ∧ d.matrixNegativeBase.length ≤ B ∧
  d.vectorPositiveBase.length ≤ B ∧ d.vectorNegativeBase.length ≤ B

theorem Data.readCap_le {m n : ℕ} (d : Data m n) (B : ℕ) (h : d.Sized B)
    (mi vi : List Bool) (hm : mi.length ≤ B) (hv : vi.length ≤ B) :
    d.readCap mi vi ≤ 80000*(B+2)^2 := by
  have hwidth := h.1
  have hvalue := h.2.1
  have access (index base : List Bool) (hi : index.length ≤ B) (hb : base.length ≤ B) :
      BankArray.costCap d.width index base d.clock + 32*addressValue d.width+35 ≤
        20000*(B+2)^2 := by
    calc
      _ ≤ 1000*(B+B+B+5)^2 + B*(15*(B+B+B+1+B)+24) + 4 +
          40*(B+B+B+B+B+3) + 32*B+35 := by
        dsimp [BankArray.costCap, ArrayAccess.costCap]
        rw [d.clock_length]
        gcongr
      _ ≤ _ := by nlinarith
  have ha := access mi d.matrixPositiveBase hm h.2.2.1
  have hb := access mi d.matrixNegativeBase hm h.2.2.2.1
  have hc := access vi d.vectorPositiveBase hv h.2.2.2.2.1
  have hd := access vi d.vectorNegativeBase hv h.2.2.2.2.2
  dsimp [Data.readCap]
  omega

theorem canonical_length_le (bits : List Bool) : (addressValue bits).bits.length ≤ bits.length := by
  rw [Nat.size_eq_bits_len]
  exact Nat.size_le.mpr (IndexedAddress.value_lt_pow_length bits)

def indexedTermCode : Code := .seq loadTermCode termCode

/-- Four actual indexed reads feed the signed arithmetic kernel. The arrays
and layout words remain fixed; only the two running sums change. -/
theorem indexed_term {m n : ℕ} (d : Data m n) (B : ℕ) (hsized : d.Sized B)
    (input : List Bool) (tape : ℕ → Bool) (mi vi : List Bool)
    (hmiLen : mi.length ≤ B) (hviLen : vi.length ≤ B) (i : Fin m) (j : Fin n)
    (hmi : addressValue mi = i.val) (hvi : addressValue vi = j.val)
    (positive negative : ℕ) (hp : positive.bits.length ≤ B) (hn : negative.bits.length ≤ B)
    (s : Store) (hready : Ready s.val (dotValues positive negative))
    (hdata : Stored d s.val) (hindices : Indices s.val mi vi) :
    ∃ cost, ∃ t : Store, cost ≤ 500000*(B+2)^2 ∧ Executes input tape indexedTermCode cost s t ∧
      Ready t.val (dotValues (positive+d.positiveTerm i j) (negative+d.negativeTerm i j)) ∧
      StepFrame s.val t.val := by
  obtain ⟨rcost, r, hrcost, hr, hrr, hrf⟩ := load_term d input tape mi vi i j hmi hvi
    positive negative s hready hdata hindices
  have hap : (addressValue (d.matrixPositive.get i)).bits.length ≤ B :=
    (canonical_length_le _).trans ((hdata.matrixPositive.length i).le.trans hsized.2.1)
  have han : (addressValue (d.matrixNegative.get i)).bits.length ≤ B :=
    (canonical_length_le _).trans ((hdata.matrixNegative.length i).le.trans hsized.2.1)
  have hxp : (addressValue (d.vectorPositive.get j)).bits.length ≤ B :=
    (canonical_length_le _).trans ((hdata.vectorPositive.length j).le.trans hsized.2.1)
  have hxn : (addressValue (d.vectorNegative.get j)).bits.length ≤ B :=
    (canonical_length_le _).trans ((hdata.vectorNegative.length j).le.trans hsized.2.1)
  have hbits : ∀ k, 30 ≤ k → k ≤ 35 →
      (termValues positive negative (addressValue (d.matrixPositive.get i))
        (addressValue (d.matrixNegative.get i)) (addressValue (d.vectorPositive.get j))
        (addressValue (d.vectorNegative.get j)) k).bits.length ≤ B := by
    intro k hk hk'
    interval_cases k <;> simpa [termValues, dotValues]
  obtain ⟨tcost, t, htcost, ht, htr, htf⟩ := term input tape positive negative
    (addressValue (d.matrixPositive.get i)) (addressValue (d.matrixNegative.get i))
    (addressValue (d.vectorPositive.get j)) (addressValue (d.vectorNegative.get j)) B hbits r hrr
  refine ⟨rcost+tcost, t, ?_, hr.seq ht, ?_, hrf.trans htf⟩
  · have hb := d.readCap_le B hsized mi vi hmiLen hviLen
    nlinarith
  · simpa only [Data.positiveTerm, Data.negativeTerm, Nat.add_assoc] using htr

end Maxwell.Cost.CalibrationMatrix
