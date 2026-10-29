import Maxwell.Cost.BinaryPrecision
import Maxwell.Green.CalibrationInteger

/-! A literal finite decision tree for the fixed periodic material table.
Its key is consumed by actual reads, erases and moves; its leaves emit only
platform constants. There is no run-time matrix or material oracle. -/
namespace Maxwell.Cost.CalibrationMatrix.MaterialTable
open Structured
open RationalAccumulator (Word Blank)
set_option maxHeartbeats 800000

/-- The two components are the nonnegative channels of a fixed integer. -/
def code (key positive negative : ℕ) : ℕ → (List Bool → ℕ × ℕ) → Code
  | 0, table => .seq (BinaryPrecision.literalCode positive (table []).1)
      (BinaryPrecision.literalCode negative (table []).2)
  | depth + 1, table =>
      .seq (Code.atom (.readTape key 0 1))
        (.seq (Code.atom (.eraseTape key))
          (.seq (Code.atom (.tapeRight key))
            (.branch 0 (code key positive negative depth (fun bs => table (true :: bs)))
              (code key positive negative depth (fun bs => table (false :: bs))))))

abbrev Frame (key positive negative : ℕ) := BinaryPrecision.Frame {key, positive, negative}

private def readState (key : ℕ) (s : Store) : Store :=
  Store.ofState {s.val.setRegister 0 ((s.val.tapes key).read.getD false) with
    registers := Function.update (Function.update s.val.registers 0
      ((s.val.tapes key).read.getD false)) 1 ((s.val.tapes key).read.isSome)}

private theorem read_executes (key : ℕ) (input : List Bool) (randomTape : ℕ → Bool)
    (s : Store) : Executes input randomTape (Code.atom (.readTape key 0 1)) 3 s
      (readState key s) := by
  apply Executes.atom (extra := 1)
  · simp [BitRAM.next, s.property]
  · simp [BitRAMState.setRegister, s.property]

/-- Every queried key follows a fixed finite branch tree. The charge is
linear in the key and the two emitted integer bit lengths. -/
theorem executes (key positive negative : ℕ)
    (hkp : key ≠ positive) (hkn : key ≠ negative) (hpn : positive ≠ negative)
    (input : List Bool) (randomTape : ℕ → Bool) (bits : List Bool)
    (table : List Bool → ℕ × ℕ) (origin : ℤ) (s : Store)
    (hkey : s.val.tapes key = BitTape.shifted bits origin)
    (hp : Blank s.val positive) (hn : Blank s.val negative) :
    ∃ t, Executes input randomTape (code key positive negative bits.length table)
        (8 * bits.length + 10 * ((table bits).1.size + (table bits).2.size) + 14) s t ∧
      Word t.val positive (table bits).1 ∧ Word t.val negative (table bits).2 ∧
      t.val.tapes key = {BitTape.blank with head := origin + bits.length} ∧
      Frame key positive negative s.val t.val := by
  induction bits generalizing table origin s with
  | nil =>
      obtain ⟨a, ea, ha, fa⟩ := BinaryPrecision.literal positive (table []).1 input randomTape s hp
      have han : Blank a.val negative := RationalAccumulator.blank_of_eq
        (fa.tapes negative (by simp [Ne.symm hpn])) hn
      obtain ⟨t, et, ht, ft⟩ := BinaryPrecision.literal negative (table []).2 input randomTape a han
      refine ⟨t, ?_, RationalAccumulator.word_of_eq (ft.tapes positive (by simp [hpn])) ha,
        ht, ?_, (fa.mono (by simp)).trans (ft.mono (by simp))⟩
      · convert ea.seq et using 1
        · rfl
        · simp only [List.length_nil, Nat.size_eq_bits_len]
          omega
      · simpa using (ft.tapes key (by simp [hkn])).trans
          ((fa.tapes key (by simp [hkp])).trans hkey)
  | cons b bits ih =>
      let r := readState key s
      let e := Store.ofState (r.val.setTape key ((r.val.tapes key).write none))
      let a := Store.ofState (e.val.setTape key
        {e.val.tapes key with head := (e.val.tapes key).head + 1})
      have er := read_executes key input randomTape s
      have ee : Executes input randomTape (Code.atom (.eraseTape key)) 2 r e :=
        Executes.eraseTape input randomTape r key
      have ea : Executes input randomTape (Code.atom (.tapeRight key)) 2 e a :=
        Executes.tapeRight input randomTape e key
      have haKey : a.val.tapes key = BitTape.shifted bits (origin + 1) := by
        simpa [a, e, r, readState, Store.ofState, BitRAMState.setTape,
          BitRAMState.setRegister, hkey, BitTape.write, BitTape.shifted] using
          BitTape.shifted_erase_move b bits origin
      have haReg : a.val.registers 0 = b := by
        simp [a, e, r, readState, Store.ofState, BitRAMState.setTape,
          BitRAMState.setRegister, hkey]
      have fa : BinaryPrecision.Frame {key} s.val a.val := by
        refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
        intro i hi
        have hi' : i ≠ key := by simpa using hi
        simp [a, e, r, readState, Store.ofState, BitRAMState.setTape,
          BitRAMState.setRegister, hi']
      have hap := RationalAccumulator.blank_of_eq (fa.tapes positive (by simp [Ne.symm hkp])) hp
      have han := RationalAccumulator.blank_of_eq (fa.tapes negative (by simp [Ne.symm hkn])) hn
      obtain ⟨t, et, htp, htn, htk, ft⟩ := ih (fun bs => table (b :: bs)) (origin + 1) a haKey hap han
      have branch : Executes input randomTape
          (.branch 0 (code key positive negative bits.length (fun bs => table (true :: bs)))
            (code key positive negative bits.length (fun bs => table (false :: bs))))
          (1 + (8 * bits.length + 10 * ((table (b :: bits)).1.size +
            (table (b :: bits)).2.size) + 14)) a t := by
        cases b
        · exact .no haReg et
        · exact .yes haReg et
      refine ⟨t, ?_, htp, htn, ?_, (fa.mono (by simp)).trans ft⟩
      · convert er.seq (ee.seq (ea.seq branch)) using 1 <;>
          first | rfl | simp only [List.length_cons]; omega
      · simpa only [List.length_cons, Nat.cast_add, Nat.cast_one, add_assoc,
          add_left_comm, add_comm] using htk

/-- A fixed material table has a fixed output-width bound; lookup work is
therefore bounded independently of the finite cube dimension. -/
theorem cost_bound (bits : List Bool) (table : List Bool → ℕ × ℕ) (B : ℕ)
    (hb : (table bits).1.size + (table bits).2.size ≤ B) :
    8 * bits.length + 10 * ((table bits).1.size + (table bits).2.size) + 14 ≤
      8 * bits.length + 10 * B + 14 := by omega

/-- A computable maximum over the fixed literal branch tree. This uses
structural recursion, so its definition never enumerates run-time inputs. -/
def outputBits : ℕ → (List Bool → ℕ × ℕ) → ℕ
  | 0, table => (table []).1.size + (table []).2.size
  | depth + 1, table => max (outputBits depth (fun bs => table (true :: bs)))
      (outputBits depth (fun bs => table (false :: bs)))

theorem outputBits_bound (bits : List Bool) (table : List Bool → ℕ × ℕ) :
    (table bits).1.size + (table bits).2.size ≤ outputBits bits.length table := by
  induction bits generalizing table with
  | nil => exact le_rfl
  | cons b bits ih =>
    cases b
    · exact (ih (fun bs => table (false :: bs))).trans (le_max_right _ _)
    · exact (ih (fun bs => table (true :: bs))).trans (le_max_left _ _)

/-- Actual cost depends only on the fixed table and its fixed key width. -/
theorem fixed_cost_bound (bits : List Bool) (table : List Bool → ℕ × ℕ) :
    8 * bits.length + 10 * ((table bits).1.size + (table bits).2.size) + 14 ≤
      8 * bits.length + 10 * outputBits bits.length table + 14 :=
  cost_bound bits table _ (outputBits_bound bits table)

end Maxwell.Cost.CalibrationMatrix.MaterialTable
