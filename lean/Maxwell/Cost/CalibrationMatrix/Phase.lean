import Maxwell.Cost.CalibrationMatrix.MaterialTable
import Maxwell.Cost.CalibrationMatrix.TableKey

/-! Constant-size residue subtraction for the physical period-20 cell. -/
namespace Maxwell.Cost.CalibrationMatrix.Phase
open Structured RationalAccumulator

/-- Nonnegative subtraction using only two residues in the fixed range. -/
def phase (x r : ℕ) : ℕ := (x + 20 - r) % 20

theorem phase_lt (x r : ℕ) : phase x r < 20 := Nat.mod_lt _ (by decide)

theorem phase_bits (x r : ℕ) : (phase x r).size ≤ 5 := by
  apply Nat.size_le.mpr
  have h := phase_lt x r
  norm_num
  omega

/-- The residue correction exactly restores the signed cube coordinate. -/
theorem phase_value (x R : ℕ) : phase (x % 20) (R % 20) = ((x : ZMod 20) - (R : ZMod 20)).val := by
  have hle : R % 20 ≤ x % 20 + 20 := by have h := Nat.mod_lt R (by decide : 0 < 20); omega
  have hcast : (phase (x % 20) (R % 20) : ZMod 20) = (x : ZMod 20) - (R : ZMod 20) := by
    rw [phase, ZMod.natCast_mod, Nat.cast_sub hle, Nat.cast_add, ZMod.natCast_mod, ZMod.natCast_mod]
    rw [ZMod.natCast_self, add_zero]
  have hv := congrArg ZMod.val hcast
  simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt (phase_lt _ _)] using hv

def table (bits : List Bool) : ℕ × ℕ :=
  (phase (addressValue (bits.take 5)) (addressValue (bits.drop 5)), 0)

def encode (x r : ℕ) : List Bool := TableKey.field 5 x ++ TableKey.field 5 r

@[simp] theorem encode_length (x r : ℕ) : (encode x r).length = 10 := by simp [encode]

theorem table_encode (x r : ℕ) (hx : x < 20) (hr : r < 20) :
    table (encode x r) = (phase x r, 0) := by
  have hxs : x.size ≤ 5 := Nat.size_le.mpr (by norm_num; omega)
  have hrs : r.size ≤ 5 := Nat.size_le.mpr (by norm_num; omega)
  have hp : (encode x r).take 5 = TableKey.field 5 x := by
    simpa only [encode, TableKey.field_length] using
      (show (TableKey.field 5 x ++ TableKey.field 5 r).take (TableKey.field 5 x).length = _ from List.take_left)
  have hs : (encode x r).drop 5 = TableKey.field 5 r := by
    simpa only [encode, TableKey.field_length] using
      (show (TableKey.field 5 x ++ TableKey.field 5 r).drop (TableKey.field 5 x).length = _ from List.drop_left)
  simp only [table, hp, hs, TableKey.field_value 5 x hxs, TableKey.field_value 5 r hrs]

def code (key result zeroBank : ℕ) : Code := MaterialTable.code key result zeroBank 10 table

/-- Actual lookup of the fixed 20-by-20 subtraction table. The two input
residues are read as ten bits; canonical output and scratch-zeroBank are emitted. -/
theorem executes (key result zeroBank : ℕ) (hkr : key ≠ result) (hkz : key ≠ zeroBank) (hrz : result ≠ zeroBank)
    (input : List Bool) (tape : ℕ → Bool) (x r : ℕ) (hx : x < 20) (hr : r < 20)
    (origin : ℤ) (s : Store) (hkey : s.val.tapes key = BitTape.shifted (encode x r) origin)
    (hresult : Blank s.val result) (hzero : Blank s.val zeroBank) :
    ∃ cost t, cost ≤ 144 ∧ Executes input tape (code key result zeroBank) cost s t ∧
      Word t.val result (phase x r) ∧ Blank t.val zeroBank ∧
      t.val.tapes key = {BitTape.blank with head := origin + 10} ∧
      MaterialTable.Frame key result zeroBank s.val t.val := by
  obtain ⟨t, he, ht, hz, hk, hf⟩ := MaterialTable.executes key result zeroBank hkr hkz hrz
    input tape (encode x r) table origin s hkey hresult hzero
  have hb := phase_bits x r
  rw [table_encode x r hx hr] at he ht hz
  simp only [encode_length, Nat.size_zero, Nat.add_zero] at he
  refine ⟨8 * 10 + 10 * (phase x r).size + 14, t, by omega, he, ht, ?_, ?_, hf⟩
  · simpa [Word, Blank, Nat.zero_bits] using hz
  · simpa only [encode_length, Nat.cast_ofNat] using hk

end Maxwell.Cost.CalibrationMatrix.Phase
