import Maxwell.Cost.CalibrationSource.RepackPass
import Maxwell.Cost.CalibrationSource.IndexArray
import Maxwell.Cost.CalibrationSource.Meaning

namespace Maxwell.Cost.CalibrationSource.Producer
open Structured CalibrationMatrix
open RationalAccumulator (Blank)
set_option maxHeartbeats 1000000

def indexData (c : Repack.Data) (base : List Bool) : IndexArray.Data :=
  ⟨c.width,c.clock,base,c.width_nonempty,c.width_positive,c.clock_length⟩

def work : Finset ℕ := IndexArray.work ∪ {30,31,32,33,34,35,36,104}

structure Frame (s t : BitRAMState) : Prop where
  inputHead : t.inputHead = s.inputHead
  randomCursor : t.randomCursor = s.randomCursor
  output : t.output = s.output
  tapes : ∀ j, j ∉ work → t.tapes j = s.tapes j

def Outside (c : Repack.Data) (base : List Bool) (m : ℕ) (s t : BitRAMState) : Prop :=
  ∀ a, (a < addressValue base ∨ addressValue base+m*addressValue c.width ≤ a) →
    (a < addressValue (c.bases 0) ∨ addressValue (c.bases 0)+m*addressValue c.width ≤ a) →
    (a < addressValue (c.bases 1) ∨ addressValue (c.bases 1)+m*addressValue c.width ≤ a) →
    t.memory a = s.memory a

structure Separated {m : ℕ} (c : Repack.Data) (base : List Bool) (d : ModeRead.Data m) : Prop where
  coefficients : c.Separated d
  index_coefficients : ∀ a, IncidenceEncoding.Separated (addressValue base) (m*addressValue c.width)
    (addressValue (c.bases a)) (m*addressValue c.width)
  mode_index : ∀ a, IncidenceEncoding.Separated (addressValue (d.bases a)) (m*addressValue d.width)
    (addressValue base) (m*addressValue c.width)

theorem represents_after_index {m n : ℕ} {c : IndexArray.Data} {base width : ℕ}
    {values : Vector (List Bool) n} {s t : BitRAMState}
    (h : BitArray.Represents s.memory base width values) (hout : IndexArray.Outside c m s t)
    (hsep : IncidenceEncoding.Separated base (n*width) (addressValue c.base) (m*addressValue c.width)) :
    BitArray.Represents t.memory base width values := by
  refine ⟨h.length,?_⟩
  intro i j hj
  rw [hout]
  · exact h.bits i j hj
  · have hs := Nat.mul_le_mul_right width (show i.val+1 ≤ n by omega)
    rcases hsep with hsep | hsep
    · left; nlinarith
    · right; omega

theorem represents_after_repack {m n : ℕ} {c : Repack.Data} {base width : ℕ}
    {values : Vector (List Bool) n} {s t : BitRAMState}
    (h : BitArray.Represents s.memory base width values)
    (hout : OutputOutside c.output m (addressValue c.width) s t)
    (hsep : ∀ a, IncidenceEncoding.Separated base (n*width)
      (addressValue (c.bases a)) (m*addressValue c.width)) :
    BitArray.Represents t.memory base width values := by
  refine ⟨h.length,?_⟩
  intro i j hj
  have hs := Nat.mul_le_mul_right width (show i.val+1 ≤ n by omega)
  have outside (a : Fin 2) : base+i.val*width+j < addressValue (c.bases a) ∨
      addressValue (c.bases a)+m*addressValue c.width ≤ base+i.val*width+j := by
    rcases hsep a with hsep | hsep
    · left; nlinarith
    · right; omega
  rw [hout _ (outside 0) (outside 1)]
  exact h.bits i j hj

theorem modeStored_after_index {m : ℕ} {c : Repack.Data} {base : List Bool} {d : ModeRead.Data m}
    {s t : BitRAMState} (h : ModeRead.Stored Repack.readLayout d s)
    (hf : IndexArray.Frame s t) (hout : IndexArray.Outside (indexData c base) m s t)
    (hsep : ∀ a, IncidenceEncoding.Separated (addressValue (d.bases a)) (m*addressValue d.width)
      (addressValue base) (m*addressValue c.width)) : ModeRead.Stored Repack.readLayout d t := by
  have keep (j : ℕ) (hj : 510 ≤ j) : t.tapes j = s.tapes j := by
    apply hf.tapes
    simp [IndexArray.work,IndexArray.cleanup] 
    omega
  refine ⟨BankArray.word_of_eq (keep 514 (by omega)) h.width,
    BankArray.word_of_eq (keep 515 (by omega)) h.clock,?_,
    RationalAccumulator.word_of_eq (keep 512 (by omega)) h.denominator,?_⟩
  · intro a; apply BankArray.word_of_eq (keep _ _) (h.bases a)
    fin_cases a <;> decide
  · intro a; exact represents_after_index (h.arrays a) hout (hsep a)

end Maxwell.Cost.CalibrationSource.Producer
