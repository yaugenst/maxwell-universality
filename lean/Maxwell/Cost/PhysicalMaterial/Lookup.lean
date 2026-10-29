import Maxwell.Cost.PhysicalMaterial.Key
import Maxwell.Cost.CalibrationMatrix.MaterialTable

/-! Periodic material lookup from actual runtime coordinates. -/
namespace Maxwell.Cost.PhysicalMaterial
open Structured RationalAccumulator Maxwell.Spectral.Lattice
set_option maxHeartbeats 1000000

def decodeKey (bits : List Bool) : Cell20 :=
  ![(addressValue (bits.take 5) : ZMod 20),
    (addressValue ((bits.drop 5).take 5) : ZMod 20),
    (addressValue (bits.drop 10) : ZMod 20)]

private theorem remainder_size (n : ℕ) : (n % 20).size ≤ 5 := by
  apply Nat.size_le.mpr
  have h := Nat.mod_lt n (by decide : 0 < 20)
  norm_num
  omega

private theorem field_prefix (n : ℕ) (rest : List Bool) :
    (CalibrationMatrix.TableKey.field 5 n ++ rest).take 5 =
      CalibrationMatrix.TableKey.field 5 n := by
  simpa only [CalibrationMatrix.TableKey.field_length] using
    (show (CalibrationMatrix.TableKey.field 5 n ++ rest).take
      (CalibrationMatrix.TableKey.field 5 n).length =
      CalibrationMatrix.TableKey.field 5 n from List.take_left)

private theorem field_suffix (n : ℕ) (rest : List Bool) :
    (CalibrationMatrix.TableKey.field 5 n ++ rest).drop 5 = rest := by
  simpa only [CalibrationMatrix.TableKey.field_length] using
    (show (CalibrationMatrix.TableKey.field 5 n ++ rest).drop
      (CalibrationMatrix.TableKey.field 5 n).length = rest from List.drop_left)

/-- The decoding identity is only used in the proof; execution reads fifteen
ordinary Boolean cells and follows a fixed finite branch tree. -/
theorem decode_keyBits (x y z : ℕ) : decodeKey (keyBits x y z) =
    ![(x : ZMod 20), (y : ZMod 20), (z : ZMod 20)] := by
  have h5 : (keyBits x y z).drop 5 =
      CalibrationMatrix.TableKey.field 5 (y % 20) ++
      CalibrationMatrix.TableKey.field 5 (z % 20) := field_suffix _ _
  have h10 : (keyBits x y z).drop 10 = CalibrationMatrix.TableKey.field 5 (z % 20) := by
    rw [show (10 : ℕ) = 5 + 5 from rfl, ← List.drop_drop, h5, field_suffix]
  funext j
  fin_cases j
  · change (addressValue ((keyBits x y z).take 5) : ZMod 20) = x
    rw [keyBits, field_prefix, CalibrationMatrix.TableKey.field_value 5 _ (remainder_size _)]
    simp
  · change (addressValue (((keyBits x y z).drop 5).take 5) : ZMod 20) = y
    rw [h5, field_prefix, CalibrationMatrix.TableKey.field_value 5 _ (remainder_size _)]
    simp
  · change (addressValue ((keyBits x y z).drop 10) : ZMod 20) = z
    rw [h10, CalibrationMatrix.TableKey.field_value 5 _ (remainder_size _)]
    simp

def materialTable (material : Cell20 → ℚ) (bits : List Bool) : ℕ × ℕ :=
  ((material (decodeKey bits)).num.toNat, (material (decodeKey bits)).den)

def lookupCode (material : Cell20 → ℚ) : Code :=
  .seq keyCode (CalibrationMatrix.MaterialTable.code 247 270 271 15 (materialTable material))

def lookupWork : Finset ℕ := keyWork ∪ {270, 271}

def lookupBudget (material : Cell20 → ℚ) (x y z : ℕ) : ℕ :=
  keyBudget x y z + 134 + 10 * CalibrationMatrix.MaterialTable.outputBits 15 (materialTable material)

/-- The actual finite lookup program emits the numerator and denominator of
the fixed periodic background at the actual stored cell coordinates. -/
theorem lookup_executes (material : Cell20 → ℚ) (input : List Bool) (tape : ℕ → Bool)
    (x y z : ℕ) (s : Store) (hx : Word s.val 240 x) (hy : Word s.val 241 y)
    (hz : Word s.val 242 z) (hperiod : Word s.val 243 20) (hclock : Word s.val 249 16)
    (hblank : ∀ i, i < 5 → Blank s.val i)
    (h244 : Blank s.val 244) (h247 : Blank s.val 247) (h248 : Blank s.val 248)
    (h270 : Blank s.val 270) (h271 : Blank s.val 271) :
    ∃ cost t, cost ≤ lookupBudget material x y z ∧
      Executes input tape (lookupCode material) cost s t ∧
      Word t.val 270 (material ![(x : ZMod 20), (y : ZMod 20), (z : ZMod 20)]).num.toNat ∧
      Word t.val 271 (material ![(x : ZMod 20), (y : ZMod 20), (z : ZMod 20)]).den ∧
      (∀ i, i < 5 → Blank t.val i) ∧ Blank t.val 244 ∧ Blank t.val 247 ∧ Blank t.val 248 ∧
      BinaryPrecision.Frame lookupWork s.val t.val := by
  obtain ⟨kc, a, hkc, ek, ⟨origin, hak⟩, ha0, ha244, ha248, fa⟩ :=
    key_executes input tape x y z s hx hy hz hperiod hclock hblank h244 h247 h248
  obtain ⟨t, et, ht270, ht271, htk, ft⟩ := CalibrationMatrix.MaterialTable.executes
    247 270 271 (by decide) (by decide) (by decide) input tape (keyBits x y z)
    (materialTable material) origin a hak
    (blank_of_eq (fa.tapes 270 (by decide)) h270)
    (blank_of_eq (fa.tapes 271 (by decide)) h271)
  have bound := CalibrationMatrix.MaterialTable.fixed_cost_bound (keyBits x y z)
    (materialTable material)
  have htable : materialTable material (keyBits x y z) =
      ((material ![(x : ZMod 20), (y : ZMod 20), (z : ZMod 20)]).num.toNat,
       (material ![(x : ZMod 20), (y : ZMod 20), (z : ZMod 20)]).den) := by
    rw [materialTable, decode_keyBits]
  refine ⟨kc + (8 * (keyBits x y z).length +
      10 * ((materialTable material (keyBits x y z)).1.size +
        (materialTable material (keyBits x y z)).2.size) + 14), t, ?_, ?_,
    by simpa only [htable] using ht270, by simpa only [htable] using ht271,
    ?_, blank_of_eq (ft.tapes 244 (by decide)) ha244, ⟨origin + (keyBits x y z).length, htk⟩,
    blank_of_eq (ft.tapes 248 (by decide)) ha248, ?_⟩
  · simp only [keyBits_length] at bound ⊢
    dsimp only [lookupBudget]
    omega
  · simpa only [lookupCode, keyBits_length] using ek.seq et
  · intro i hi
    exact blank_of_eq (ft.tapes i (by simp; omega)) (ha0 i hi)
  · exact (fa.mono Finset.subset_union_left).trans (ft.mono (by decide))

/-- Nonnegative background entries are represented exactly by the emitted
unsigned pair; positivity of its denominator is intrinsic to rationals. -/
theorem materialTable_value (material : Cell20 → ℚ) (hm : ∀ c, 0 ≤ material c)
    (bits : List Bool) :
    ((materialTable material bits).1 : ℚ) / (materialTable material bits).2 =
      material (decodeKey bits) ∧ 0 < (materialTable material bits).2 := by
  have hn : 0 ≤ (material (decodeKey bits)).num := Rat.num_nonneg.mpr (hm _)
  constructor
  · dsimp only [materialTable]
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hn, Rat.num_div_den]
  · exact (material (decodeKey bits)).pos

end Maxwell.Cost.PhysicalMaterial
