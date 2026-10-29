import Maxwell.Cost.PhysicalMaterial.Coordinate

namespace Maxwell.Cost.PhysicalMaterial
open Structured RationalAccumulator
set_option maxHeartbeats 1000000

def keyBits (x y z : ℕ) : List Bool :=
  CalibrationMatrix.TableKey.field 5 (x % 20) ++
  (CalibrationMatrix.TableKey.field 5 (y % 20) ++
   CalibrationMatrix.TableKey.field 5 (z % 20))

@[simp] theorem keyBits_length (x y z : ℕ) : (keyBits x y z).length = 15 := by
  simp [keyBits]

def keyCode : Code :=
  .seq (coordinateCode 240)
    (.seq (coordinateCode 241)
      (.seq (coordinateCode 242) (.call (Rewind.program 247))))

def keyBudget (x y z : ℕ) : ℕ :=
  700 * ((x.bits.length + 8)^2 + (y.bits.length + 8)^2 + (z.bits.length + 8)^2) + 636

/-- The complete cell key is computed from the three runtime coordinate words.
No key bits or material values are supplied as machine inputs. -/
theorem key_executes (input : List Bool) (tape : ℕ → Bool) (x y z : ℕ) (s : Store)
    (hx : Word s.val 240 x) (hy : Word s.val 241 y) (hz : Word s.val 242 z)
    (hperiod : Word s.val 243 20) (hclock : Word s.val 249 16)
    (hblank : ∀ i, i < 5 → Blank s.val i)
    (h244 : Blank s.val 244) (h247 : Blank s.val 247) (h248 : Blank s.val 248) :
    ∃ cost t, cost ≤ keyBudget x y z ∧ Executes input tape keyCode cost s t ∧
      BankArray.Word t.val 247 (keyBits x y z) ∧
      (∀ i, i < 5 → Blank t.val i) ∧ Blank t.val 244 ∧ Blank t.val 248 ∧
      BinaryPrecision.Frame keyWork s.val t.val := by
  obtain ⟨origin, ho⟩ := h247
  obtain ⟨xc, a, hxc, ex, hak, ha0, ha244, ha248, fa⟩ := append_coordinate 240
    (by decide) input tape x [] origin s hx hperiod hclock hblank h244 h248 (by simpa using ho)
  obtain ⟨yc, b, hyc, ey, hbk, hb0, hb244, hb248, fb⟩ := append_coordinate 241
    (by decide) input tape y (CalibrationMatrix.TableKey.field 5 (x % 20)) origin a
    (word_of_eq (fa.tapes 241 (by decide)) hy)
    (word_of_eq (fa.tapes 243 (by decide)) hperiod)
    (word_of_eq (fa.tapes 249 (by decide)) hclock) ha0 ha244 ha248 (by simpa using hak)
  have fab := fa.trans fb
  obtain ⟨zc, c, hzc, ez, hck, hc0, hc244, hc248, fc⟩ := append_coordinate 242
    (by decide) input tape z
    (CalibrationMatrix.TableKey.field 5 (x % 20) ++ CalibrationMatrix.TableKey.field 5 (y % 20))
    origin b (word_of_eq (fab.tapes 242 (by decide)) hz)
    (word_of_eq (fab.tapes 243 (by decide)) hperiod)
    (word_of_eq (fab.tapes 249 (by decide)) hclock) hb0 hb244 hb248 hbk
  have hword : c.val.tapes 247 = BitTape.shiftedEnd (keyBits x y z) origin := by
    simpa only [keyBits, List.append_assoc] using hck
  have hr := WordTransfer.rewind_shifted 247 origin input tape (keyBits x y z)
    c.val c.property hword
  let t := Store.ofState (Rewind.finishAt 247 origin c.val)
  have er : Executes input tape (.call (Rewind.program 247))
      (4 * (keyBits x y z).length + 6) c t :=
    .call _ c _ _ hr.1 (by simp [Rewind.program, Rewind.finishAt])
  have keep (i : ℕ) (hi : i ≠ 247) : t.val.tapes i = c.val.tapes i := by
    simp [t, Store.ofState, Rewind.finishAt, hi]
  have ft : BinaryPrecision.Frame keyWork c.val t.val := by
    refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
    intro i hi
    exact keep i (by intro he; subst i; exact hi (by simp [keyWork]))
  refine ⟨xc + (yc + (zc + (4 * (keyBits x y z).length + 6))), t, ?_,
    ex.seq (ey.seq (ez.seq er)), ⟨origin, hr.2⟩, ?_,
    blank_of_eq (keep 244 (by decide)) hc244,
    blank_of_eq (keep 248 (by decide)) hc248, ((fab.trans fc).trans ft)⟩
  · rw [keyBits_length]
    dsimp only [keyBudget]
    omega
  · intro i hi
    exact blank_of_eq (keep i (by omega)) (hc0 i hi)

end Maxwell.Cost.PhysicalMaterial
