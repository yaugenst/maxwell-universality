import Maxwell.Cost.Counter
import Maxwell.Cost.Division
import Maxwell.Cost.WordCall
import Maxwell.Cost.ScanForward
import Maxwell.Green.CalibrationIndex

/-! Actual binary mixed-radix extraction for finite stencil-array generation. -/
namespace Maxwell.Cost.CalibrationMatrix.Entry
open Structured
set_option maxHeartbeats 800000

/-- Long-division workspace, with the next dividend at its last blank cell. -/
def Prepared (s : BitRAMState) (radix dividend : List Bool) : Prop :=
  (∃ o, s.tapes 0 = {BitTape.blank with head := o}) ∧
  (∃ o, s.tapes 1 = BitTape.shifted radix o) ∧
  (∃ o, s.tapes 2 = {BitTape.blank with head := o}) ∧
  (∃ o, s.tapes 3 = BitTape.shiftedEnd dividend o) ∧
  (∃ o, s.tapes 4 = {BitTape.blank with head := o})

def Frame (target : ℕ) (s t : BitRAMState) : Prop :=
  t.address = s.address ∧ t.inputHead = s.inputHead ∧ t.memory = s.memory ∧
  t.randomCursor = s.randomCursor ∧ t.output = s.output ∧
  (∀ i, 5 ≤ i → i ≠ target → t.tapes i = s.tapes i) ∧
  (∀ i, 15 ≤ i → i ≠ 24 → i ≠ 25 → i ≠ 26 → i ≠ 27 → t.registers i = s.registers i)

theorem Frame.trans {target : ℕ} {s t u : BitRAMState}
    (h : Frame target s t) (k : Frame target t u) : Frame target s u :=
  ⟨k.1.trans h.1, k.2.1.trans h.2.1, k.2.2.1.trans h.2.2.1,
    k.2.2.2.1.trans h.2.2.2.1, k.2.2.2.2.1.trans h.2.2.2.2.1,
    fun i hi ht => (k.2.2.2.2.2.1 i hi ht).trans (h.2.2.2.2.2.1 i hi ht),
    fun i hi h24 h25 h26 h27 => (k.2.2.2.2.2.2 i hi h24 h25 h26 h27).trans
      (h.2.2.2.2.2.2 i hi h24 h25 h26 h27)⟩

private theorem frame_division {target : ℕ} {s t : BitRAMState}
    (h : Division.Frame s t) : Frame target s t :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
    fun i hi _ => h.2.2.2.2.2.2.2.1 i hi, h.2.2.2.2.2.2.2.2⟩

private theorem frame_transfer {target source dest : ℕ} {s t : BitRAMState}
    (hs : source < 5 ∨ source = target) (ht : dest < 5 ∨ dest = target)
    (h : WordTransfer.Frame source dest s t) : Frame target s t :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
    fun i hi hit => h.2.2.2.2.2.1 i (by omega) (by omega),
    fun i _ h24 h25 h26 h27 => h.2.2.2.2.2.2 i h24 h25 h26 h27⟩

/-- Divide, store the remainder digit, erase the old dividend, and prepare
the quotient for the next extraction. All moves and scans are literal code. -/
def digitCode (target : ℕ) : Code :=
  .seq (.call Division.program)
    (.seq (.call (WordTransfer.move 0 target))
      (.seq (Code.atom (.tapeRight 3))
        (.seq (.call (TapeOps.clear 3))
          (.seq (.call (WordTransfer.move 4 3)) (.call (ScanForward.program 3))))))

theorem digit (target : ℕ) (htarget : 5 ≤ target)
    (input : List Bool) (tape : ℕ → Bool) (radix dividend : List Bool)
    (hradix : 0 < addressValue radix) (s : Store) (hprep : Prepared s.val radix dividend)
    (hblank : ∃ o, s.val.tapes target = {BitTape.blank with head := o}) :
    ∃ cost t remainder quotient,
      cost ≤ 500 * (radix.length + dividend.length + 3) ^ 2 ∧
      Executes input tape (digitCode target) cost s t ∧ Prepared t.val radix quotient ∧
      (∃ o, t.val.tapes target = BitTape.shifted remainder o) ∧
      addressValue remainder = addressValue dividend % addressValue radix ∧
      addressValue quotient = addressValue dividend / addressValue radix ∧
      remainder.length ≤ radix.length + dividend.length ∧ quotient.length = dividend.length ∧
      Frame target s.val t.val := by
  obtain ⟨⟨ao, h0⟩, ⟨xo, h1⟩, ⟨zo, h2⟩, ⟨yo, h3⟩, ⟨qo, h4⟩⟩ := hprep
  obtain ⟨targetOrigin, htargetWord⟩ := hblank
  obtain ⟨dcost, divided, remainder, quotient, ro, so, qro, hdcost, ed, hdp,
    hd0, hd1, hd2, hd4, hrem, hquot, hremLength, hquotLength, hd3⟩ :=
    Division.simulation_cleanup input tape s.val radix dividend ao xo zo yo qo hradix
      s.property h0 h1 h2 h3 h4
  let d : Store := Store.ofState divided
  have ed' : Executes input tape (.call Division.program) (dcost + 1) s d :=
    .call _ s divided _ ed (by
      simp [Division.program, hdp, Subtraction.program, RewindOvershoot.program,
        RewindOvershoot.preamble, BitRAM.link, Rewind.program, TapeOps.clear,
        TapeOps.copyClear, BitRAMInstruction.relocate])
  have df := Division.execution_frame input tape ed
  have hdtarget : d.val.tapes target = {BitTape.blank with head := targetOrigin} :=
    (df.2.2.2.2.2.2.2.1 target htarget).trans htargetWord
  obtain ⟨moved, em, hmp, hm0, hmtarget, mf⟩ := WordTransfer.move_steps 0 target (by omega)
    input tape remainder ro targetOrigin d.val d.property hd0 hdtarget
  let m : Store := Store.ofState moved
  have em' : Executes input tape (.call (WordTransfer.move 0 target))
      (12 * remainder.length + 11) d m := .call _ d moved _ em (by
        simp [WordTransfer.move, hmp, TapeOps.copyClear, Rewind.program, BitRAMInstruction.relocate])
  let r : Store := Store.ofState (m.val.setTape 3
    {m.val.tapes 3 with head := (m.val.tapes 3).head + 1})
  have er : Executes input tape (Code.atom (.tapeRight 3)) 2 m r := .tapeRight _ _ _ _
  have hm3 : m.val.tapes 3 = {BitTape.shifted dividend yo with head := yo - 1} :=
    (mf.2.2.2.2.2.1 3 (by omega) (by omega)).trans hd3
  have hr3 : r.val.tapes 3 = BitTape.shifted dividend yo := by
    simp [r, Store.ofState, BitRAMState.setTape, hm3, BitTape.shifted]
  obtain ⟨c, ec, hc, cf⟩ := WordCall.clear 3 input tape dividend yo r hr3
  have hc3 : c.val.tapes 3 = {BitTape.blank with head := yo + dividend.length} := by simp [hc]
  have hc4 : c.val.tapes 4 = BitTape.shifted quotient qro := by
    rw [hc]
    simpa [r, m, Store.ofState, BitRAMState.setTape] using
      (mf.2.2.2.2.2.1 4 (by omega) (by omega)).trans hd4
  obtain ⟨next, en, hnp, hn4, hn3, nf⟩ := WordTransfer.move_steps 4 3 (by omega)
    input tape quotient qro (yo + dividend.length) c.val c.property hc4 hc3
  let q : Store := Store.ofState next
  have en' : Executes input tape (.call (WordTransfer.move 4 3))
      (12 * quotient.length + 11) c q := .call _ c next _ en (by
        simp [WordTransfer.move, hnp, TapeOps.copyClear, Rewind.program, BitRAMInstruction.relocate])
  have scan := ScanForward.shifted_steps 3 (yo + dividend.length) input tape quotient
    q.val q.property hn3
  let t : Store := Store.ofState (ScanForward.finish 3 quotient.length q.val)
  have es : Executes input tape (.call (ScanForward.program 3)) (5 * quotient.length + 4) q t :=
    .call _ q _ _ scan.1 (by simp [ScanForward.program, ScanForward.finish])
  have rf : Frame target m.val r.val := by
    refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, fun _ _ _ _ _ _ => rfl⟩
    intro i hi _
    simp [r, Store.ofState, BitRAMState.setTape, show i ≠ 3 by omega]
  have finalFrame : Frame target s.val t.val :=
    (((((frame_division df).trans (frame_transfer (Or.inl (by omega)) (Or.inr rfl) mf)).trans rf).trans
      (frame_transfer (Or.inl (by omega)) (Or.inl (by omega)) (WordTransfer.frame_of_copy cf))).trans
      (frame_transfer (Or.inl (by omega)) (Or.inl (by omega)) nf)).trans
      (frame_transfer (Or.inl (by omega)) (Or.inl (by omega)) (WordTransfer.frame_of_copy scan.2.2))
  have keep (i : ℕ) (hi : i ≠ 3) (hi4 : i ≠ 4) : t.val.tapes i = m.val.tapes i := by
    have hs : t.val.tapes i = q.val.tapes i := scan.2.2.2.2.2.2.2.1 i hi hi
    have hn : q.val.tapes i = c.val.tapes i := nf.2.2.2.2.2.1 i hi4 hi
    have hc' : c.val.tapes i = r.val.tapes i := cf.2.2.2.2.2.1 i hi hi
    have hr : r.val.tapes i = m.val.tapes i := by
      simp [r, Store.ofState, BitRAMState.setTape, hi]
    exact hs.trans (hn.trans (hc'.trans hr))
  refine ⟨dcost + 1 + (12 * remainder.length + 11 +
    (2 + (6 * dividend.length + 4 + (12 * quotient.length + 11 + (5 * quotient.length + 4))))),
    t, remainder, quotient, ?_, ed'.seq (em'.seq (er.seq (ec.seq (en'.seq es)))),
    ?_, ⟨targetOrigin, (keep target (by omega) (by omega)).trans hmtarget⟩,
    hrem, hquot, hremLength, hquotLength, finalFrame⟩
  · nlinarith
  · refine ⟨⟨ro + remainder.length, (keep 0 (by omega) (by omega)).trans hm0⟩,
      ⟨xo, (keep 1 (by omega) (by omega)).trans
        ((mf.2.2.2.2.2.1 1 (by omega) (by omega)).trans hd1)⟩,
      ⟨so, (keep 2 (by omega) (by omega)).trans
        ((mf.2.2.2.2.2.1 2 (by omega) (by omega)).trans hd2)⟩,
      ⟨yo + dividend.length, scan.2.1⟩, ⟨qro + quotient.length, ?_⟩⟩
    exact (scan.2.2.2.2.2.2.2.1 4 (by omega) (by omega)).trans hn4

/-- The decoder changes only its division workspace and its three
output digit tapes. Persistent bank words and external I/O are untouched. -/
def CubeFrame (s t : BitRAMState) : Prop :=
  t.address = s.address ∧ t.inputHead = s.inputHead ∧ t.memory = s.memory ∧
  t.randomCursor = s.randomCursor ∧ t.output = s.output ∧
  (∀ i, 5 ≤ i → i ≠ 70 → i ≠ 71 → i ≠ 72 → t.tapes i = s.tapes i) ∧
  (∀ i, 15 ≤ i → i ≠ 24 → i ≠ 25 → i ≠ 26 → i ≠ 27 → t.registers i = s.registers i)

/-- Three actual divisions extract the spatial digits in least-significant
order. The remaining quotient is the direction digit. -/
def cubeCode : Code := .seq (digitCode 70) (.seq (digitCode 71) (digitCode 72))

theorem cube_digits (input : List Bool) (tape : ℕ → Bool) (radix index : List Bool)
    (hradix : 0 < addressValue radix) (s : Store) (hprep : Prepared s.val radix index)
    (h70 : ∃ o, s.val.tapes 70 = {BitTape.blank with head := o})
    (h71 : ∃ o, s.val.tapes 71 = {BitTape.blank with head := o})
    (h72 : ∃ o, s.val.tapes 72 = {BitTape.blank with head := o}) :
    ∃ cost t x y z direction,
      cost ≤ 1500 * (radix.length + index.length + 3) ^ 2 ∧
      Executes input tape cubeCode cost s t ∧ Prepared t.val radix direction ∧
      (∃ o, t.val.tapes 70 = BitTape.shifted z o) ∧
      (∃ o, t.val.tapes 71 = BitTape.shifted y o) ∧
      (∃ o, t.val.tapes 72 = BitTape.shifted x o) ∧
      addressValue z = addressValue index % addressValue radix ∧
      addressValue y = (addressValue index / addressValue radix) % addressValue radix ∧
      addressValue x = (addressValue index / addressValue radix / addressValue radix) % addressValue radix ∧
      addressValue direction = addressValue index / addressValue radix / addressValue radix / addressValue radix ∧
      direction.length = index.length ∧
      t.val.memory = s.val.memory ∧
      (∀ i, 100 ≤ i → t.val.tapes i = s.val.tapes i) ∧
      x.length ≤ radix.length + index.length ∧
      y.length ≤ radix.length + index.length ∧
      z.length ≤ radix.length + index.length ∧ CubeFrame s.val t.val := by
  obtain ⟨c₁, s₁, z, q₁, hc₁, e₁, hp₁, hz, hzv, hq₁, hzl, hl₁, f₁⟩ :=
    digit 70 (by omega) input tape radix index hradix s hprep h70
  have h71' : ∃ o, s₁.val.tapes 71 = {BitTape.blank with head := o} := by
    simpa only [f₁.2.2.2.2.2.1 71 (by omega) (by omega)] using h71
  have h72' : ∃ o, s₁.val.tapes 72 = {BitTape.blank with head := o} := by
    simpa only [f₁.2.2.2.2.2.1 72 (by omega) (by omega)] using h72
  obtain ⟨c₂, s₂, y, q₂, hc₂, e₂, hp₂, hy, hyv, hq₂, hyl, hl₂, f₂⟩ :=
    digit 71 (by omega) input tape radix q₁ hradix s₁ hp₁ h71'
  have h72'' : ∃ o, s₂.val.tapes 72 = {BitTape.blank with head := o} := by
    simpa only [f₂.2.2.2.2.2.1 72 (by omega) (by omega)] using h72'
  obtain ⟨c₃, t, x, direction, hc₃, e₃, hp₃, hx, hxv, hdv, hxl, hld, f₃⟩ :=
    digit 72 (by omega) input tape radix q₂ hradix s₂ hp₂ h72''
  refine ⟨c₁ + (c₂ + c₃), t, x, y, z, direction, ?_, e₁.seq (e₂.seq e₃), hp₃,
    ?_, ?_, hx, hzv, ?_, ?_, ?_, hld.trans (hl₂.trans hl₁),
    f₃.2.2.1.trans (f₂.2.2.1.trans f₁.2.2.1), ?_, ?_, ?_, hzl, ?_⟩
  · rw [hl₂, hl₁] at hc₃
    rw [hl₁] at hc₂
    omega
  · obtain ⟨o, ho⟩ := hz
    exact ⟨o, (f₃.2.2.2.2.2.1 70 (by omega) (by omega)).trans
      ((f₂.2.2.2.2.2.1 70 (by omega) (by omega)).trans ho)⟩
  · obtain ⟨o, ho⟩ := hy
    exact ⟨o, (f₃.2.2.2.2.2.1 71 (by omega) (by omega)).trans ho⟩
  · simpa only [hq₁] using hyv
  · simpa only [hq₂, hq₁] using hxv
  · simpa only [hq₂, hq₁] using hdv
  · intro i hi
    exact (f₃.2.2.2.2.2.1 i (by omega) (by omega)).trans
      ((f₂.2.2.2.2.2.1 i (by omega) (by omega)).trans
        (f₁.2.2.2.2.2.1 i (by omega) (by omega)))
  · simpa only [hl₂, hl₁] using hxl
  · simpa only [hl₁] using hyl
  · refine ⟨f₃.1.trans (f₂.1.trans f₁.1),
      f₃.2.1.trans (f₂.2.1.trans f₁.2.1),
      f₃.2.2.1.trans (f₂.2.2.1.trans f₁.2.2.1),
      f₃.2.2.2.1.trans (f₂.2.2.2.1.trans f₁.2.2.2.1),
      f₃.2.2.2.2.1.trans (f₂.2.2.2.2.1.trans f₁.2.2.2.2.1), ?_, ?_⟩
    · intro i hi h70 h71 h72
      exact (f₃.2.2.2.2.2.1 i hi h72).trans
        ((f₂.2.2.2.2.2.1 i hi h71).trans (f₁.2.2.2.2.2.1 i hi h70))
    · intro i hi h24 h25 h26 h27
      exact (f₃.2.2.2.2.2.2 i hi h24 h25 h26 h27).trans
        ((f₂.2.2.2.2.2.2 i hi h24 h25 h26 h27).trans
          (f₁.2.2.2.2.2.2 i hi h24 h25 h26 h27))

open Maxwell.Defect.FiniteStencil in
/-- Exact connection between the three machine divisions and the proved
finite-cube embedding used by the physical stencil. -/
theorem radix_coordinates (R : ℕ) (i : Fin (3 * cubeWidth R ^ 3)) :
    (radixEdge R i).1.val = i.val / cubeWidth R / cubeWidth R / cubeWidth R ∧
    (radixEdge R i).2 0 = ((i.val / cubeWidth R / cubeWidth R % cubeWidth R : ℕ) : ℤ) - R ∧
    (radixEdge R i).2 1 = ((i.val / cubeWidth R % cubeWidth R : ℕ) : ℤ) - R ∧
    (radixEdge R i).2 2 = ((i.val % cubeWidth R : ℕ) : ℤ) - R := by
  constructor
  · rw [radixEdge_direction, Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]
  constructor
  · rw [radixEdge_coordinate_zero, Nat.mod_mul_left_div_self, Nat.div_div_eq_div_mul]
  constructor
  · rw [radixEdge_coordinate_one, Nat.mod_mul_left_mod, Nat.mod_mul_right_div_self]
  · rw [radixEdge_coordinate_two, Nat.mod_mul_left_mod, Nat.mod_mul_right_mod]

open Maxwell.Defect.FiniteStencil in
/-- A complete charged extraction from a genuine cube index. The emitted
unsigned coordinate digits use the common offset `R`; their exact physical
coordinates are the displayed integers. -/
theorem cube_coordinates (input : List Bool) (tape : ℕ → Bool) (R : ℕ)
    (i : Fin (3 * cubeWidth R ^ 3)) (s : Store)
    (hprep : Prepared s.val (cubeWidth R).bits i.val.bits)
    (h70 : ∃ o, s.val.tapes 70 = {BitTape.blank with head := o})
    (h71 : ∃ o, s.val.tapes 71 = {BitTape.blank with head := o})
    (h72 : ∃ o, s.val.tapes 72 = {BitTape.blank with head := o}) :
    ∃ cost t x y z direction,
      cost ≤ 1500 * (4 * (cubeWidth R).size + 5) ^ 2 ∧
      Executes input tape cubeCode cost s t ∧ Prepared t.val (cubeWidth R).bits direction ∧
      (∃ o, t.val.tapes 70 = BitTape.shifted z o) ∧
      (∃ o, t.val.tapes 71 = BitTape.shifted y o) ∧
      (∃ o, t.val.tapes 72 = BitTape.shifted x o) ∧
      addressValue direction = (radixCubeEmbedding R i).1.val ∧
      (addressValue x : ℤ) - R = (radixCubeEmbedding R i).2 0 ∧
      (addressValue y : ℤ) - R = (radixCubeEmbedding R i).2 1 ∧
      (addressValue z : ℤ) - R = (radixCubeEmbedding R i).2 2 ∧
      t.val.memory = s.val.memory ∧
      (∀ j, 100 ≤ j → t.val.tapes j = s.val.tapes j) := by
  have hradix : 0 < addressValue (cubeWidth R).bits := by
    rw [addressValue_bits]
    unfold cubeWidth
    omega
  obtain ⟨cost, t, x, y, z, direction, hc, he, hp, hz, hy, hx, hzv, hyv, hxv, hdv,
    _, hm, hmeta, _, _, _, _⟩ := cube_digits input tape (cubeWidth R).bits i.val.bits hradix s hprep h70 h71 h72
  have hi := radixIndex_bits R i
  have hlen : (cubeWidth R).bits.length + i.val.bits.length + 3 ≤
      4 * (cubeWidth R).size + 5 := by
    simp only [Nat.size_eq_bits_len]
    omega
  have hb := radix_coordinates R i
  simp only [addressValue_bits] at hzv hyv hxv hdv
  refine ⟨cost, t, x, y, z, direction,
    hc.trans (Nat.mul_le_mul_left 1500 (Nat.pow_le_pow_left hlen 2)), he, hp,
    hz, hy, hx, ?_, ?_, ?_, ?_, hm, hmeta⟩
  · exact hdv.trans hb.1.symm
  · rw [hxv]
    exact hb.2.1.symm
  · rw [hyv]
    exact hb.2.2.1.symm
  · rw [hzv]
    exact hb.2.2.2.symm

end Maxwell.Cost.CalibrationMatrix.Entry
