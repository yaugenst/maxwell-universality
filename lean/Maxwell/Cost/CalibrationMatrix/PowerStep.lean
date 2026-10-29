import Maxwell.Cost.CalibrationMatrix.Buffers
import Maxwell.Cost.CalibrationMatrix.Recycle

namespace Maxwell.Cost.CalibrationMatrix
open Structured
open RationalAccumulator (Blank)
set_option maxHeartbeats 1200000

def PowerFrame (s t : BitRAMState) : Prop :=
  t.inputHead = s.inputHead ∧ t.randomCursor = s.randomCursor ∧ t.output = s.output ∧
  (∀ i, (i = 4 ∨ 10 ≤ i) → (i < 30 ∨ 36 < i) → i ≠ 37 →
    i ≠ 102 → i ≠ 103 → i ≠ 104 → i ≠ 106 → i ≠ 108 → i ≠ 109 →
    i ≠ 112 → i ≠ 113 → i ≠ 114 → i ≠ 115 → i ≠ 140 → t.tapes i = s.tapes i) ∧
  (∀ i, 15 ≤ i → i ≠ 24 → i ≠ 25 → i ≠ 26 → i ≠ 27 → i ≠ 28 → i ≠ 29 →
    t.registers i = s.registers i)

theorem PowerFrame.refl (s : BitRAMState) : PowerFrame s s := by simp [PowerFrame]

theorem PowerFrame.trans {s t u : BitRAMState} (h : PowerFrame s t) (k : PowerFrame t u) : PowerFrame s u :=
  ⟨k.1.trans h.1, k.2.1.trans h.2.1, k.2.2.1.trans h.2.2.1,
    fun i hi hj h37 a b c d e f g j l m n =>
      (k.2.2.2.1 i hi hj h37 a b c d e f g j l m n).trans (h.2.2.2.1 i hi hj h37 a b c d e f g j l m n),
    fun i hi a b c d e f => (k.2.2.2.2 i hi a b c d e f).trans (h.2.2.2.2 i hi a b c d e f)⟩

theorem PowerFrame.of_matrix {s t : BitRAMState} (h : MatrixFrame s t) : PowerFrame s t :=
  ⟨h.1, h.2.1, h.2.2.1, fun i hi hj h37 a b c d e _ _ _ _ _ _ => h.2.2.2.1 i hi hj h37 a b c d e, h.2.2.2.2⟩

theorem PowerFrame.of_recycle {s t : BitRAMState} (h : RecycleFrame s t) : PowerFrame s t :=
  ⟨h.2.1, h.2.2.1, h.2.2.2.1,
    fun i _ _ _ h102 _ h104 _ _ h109 h112 h113 h114 h115 _ =>
      h.2.2.2.2.1 i h102 h104 h109 h112 h113 h114 h115,
    fun i _ h24 h25 h26 h27 _ _ => h.2.2.2.2.2 i h24 h25 h26 h27⟩

/-- Ready state for one product, with the source and destination buffers
represented by their actual descriptors and bit memory. -/
def Buffers.Ready {n : ℕ} (b : Buffers n) (count : List Bool) (B : ℕ) (s : BitRAMState) : Prop :=
  ∃ vi : List Bool, addressValue vi = 0 ∧ vi.length ≤ B ∧
    CalibrationMatrix.Ready s (dotValues 0 0) ∧ Stored b.data s ∧ Indices s [] vi ∧
    OutputStored b.output (addressValue b.data.width) [] b.positive b.negative s ∧
    BankArray.Word s 107 count ∧ Blank s 106 ∧ Blank s 37 ∧ Blank s 108 ∧ Blank s 109

def powerStepCode : Code := .seq (.call (WordTransfer.clone 107 108)) (.seq matvecCode recycleCode)

def powerStepCost (n B : ℕ) : ℕ := matvecCost n n B + 100*B+100

/-- The next product reads the previous output only after two charged
physical descriptor swaps. Both arithmetic and cursor scratch are restored. -/
theorem power_step {n : ℕ} (b : Buffers n) (B : ℕ) (hsized : b.Sized B)
    (hsep : b.Separated) (hfit : b.Fits) (hm : n*n < 2^B) (hn : n < 2^B)
    (hW : 0 < addressValue b.data.width) (input : List Bool) (tape : ℕ → Bool)
    (count : List Bool) (hcount : addressValue count = n) (hcl : count.length ≤ B)
    (s : Store) (hs : b.Ready count B s.val) :
    ∃ cost, ∃ t : Store, cost ≤ powerStepCost n B ∧ Executes input tape powerStepCode cost s t ∧
      b.advance.Ready count B t.val ∧ t.val.tapes 140 = s.val.tapes 140 ∧
      PowerFrame s.val t.val ∧ OutputOutside b.output n (addressValue b.data.width) s.val t.val := by
  obtain ⟨vi, hvi, hvl, hready, hdata, hidx, hout, h107, h106, h37, h108, h109⟩ := hs
  obtain ⟨co, h107⟩ := h107
  obtain ⟨oo, h108⟩ := h108
  obtain ⟨a, ea, ha, fa⟩ := WordCall.clone 107 108 (by omega) input tape count co oo s h107 h108
  have keepA (i : ℕ) (hi : i ≠ 108) : a.val.tapes i = s.val.tapes i := by simp [ha, hi]
  have frameA : MatrixFrame s.val a.val :=
    ⟨fa.2.1, fa.2.2.2.1, fa.2.2.2.2.1, fun i _ _ _ _ _ _ _ hi => keepA i hi,
      fun i _ h24 h25 h26 h27 _ _ => fa.2.2.2.2.2.2 i h24 h25 h26 h27⟩
  obtain ⟨mcost, q, fm, fv, fr, hmcost, eq, _, hfv, _, hfml, hfvl, hfrl,
    hqi, hqd, hqr, hqo, hq107, hq106, hq37, hq108, fq, hqm⟩ :=
    matvec_executes b.data b.output B hsized.1 hsized.2 hm hn hW hsep.outputs hsep.inputs
      hfit.1 hfit.2 input tape [] vi [] count count rfl hvi rfl hcount hcount (by simp) hvl
      (by simp) hcl hcl b.positive b.negative oo a
      (hready.of_tapes (fun i hi => keepA i (by omega))) (hdata.of_matrix fa.2.2.1 frameA)
      ⟨BankArray.word_of_eq (keepA 102 (by omega)) hidx.1, BankArray.word_of_eq (keepA 103 (by omega)) hidx.2⟩
      (hout.of_memory fa.2.2.1 (fun i hi => keepA i (by omega)))
      ⟨co, (keepA 107 (by omega)).trans h107⟩
      (RationalAccumulator.blank_of_eq (keepA 106 (by omega)) h106)
      (RationalAccumulator.blank_of_eq (keepA 37 (by omega)) h37) (by simp [ha])
  have keepQ (i : ℕ) (hi : i = 109 ∨ i = 140) : q.val.tapes i = a.val.tapes i :=
    fq.2.2.2.1 i (Or.inr (by omega)) (Or.inr (by omega)) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega)
  obtain ⟨t, et, ht102, ht104, ht112, ht113, ht114, ht115, ht109, ft⟩ :=
    recycle input tape fm fr b.data.vectorPositiveBase b.data.vectorNegativeBase b.output.positiveBase
      b.output.negativeBase q hqi.1 hqo.index hqd.vectorPositiveBase hqd.vectorNegativeBase
      hqo.positiveBase hqo.negativeBase
      (RationalAccumulator.blank_of_eq ((keepQ 109 (by omega)).trans (keepA 109 (by omega))) h109)
  have keepT (i : ℕ) (hi : i = 103 ∨ i = 106 ∨ i = 37 ∨ i = 108 ∨ i = 107 ∨ i = 140 ∨
      i = 100 ∨ i = 101 ∨ i = 110 ∨ i = 111) : t.val.tapes i = q.val.tapes i :=
    ft.2.2.2.2.1 i (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  refine ⟨15*count.length+17+(mcost+(6*fm.length+4+(6*fr.length+4+
      (12*(2*b.data.vectorPositiveBase.length+b.output.positiveBase.length)+33+
        (12*(2*b.data.vectorNegativeBase.length+b.output.negativeBase.length)+33))))),
    t, ?_, ea.seq (eq.seq et), ?_, ?_,
    ((PowerFrame.of_matrix frameA).trans (PowerFrame.of_matrix fq)).trans (PowerFrame.of_recycle ft),
    (OutputOutside.of_memory fa.2.2.1).trans (hqm.trans (OutputOutside.of_memory ft.1))⟩
  · rcases hsized with ⟨⟨_, _, _, _, hvp, hvn⟩, hop, hon⟩
    dsimp [powerStepCost]
    omega
  · refine ⟨fv, hfv, hfvl, hqr.of_tapes (fun i hi => ft.2.2.2.2.1 i
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)),
      ?_, ⟨ht102, BankArray.word_of_eq (keepT 103 (by omega)) hqi.2⟩, ?_,
      BankArray.word_of_eq (keepT 107 (by omega)) hq107,
      RationalAccumulator.blank_of_eq (keepT 106 (by omega)) hq106,
      RationalAccumulator.blank_of_eq (keepT 37 (by omega)) hq37,
      RationalAccumulator.blank_of_eq (keepT 108 (by omega)) hq108, ht109⟩
    · exact ⟨BankArray.word_of_eq (keepT 100 (by omega)) hqd.width,
        BankArray.word_of_eq (keepT 101 (by omega)) hqd.clock,
        BankArray.word_of_eq (keepT 110 (by omega)) hqd.matrixPositiveBase,
        BankArray.word_of_eq (keepT 111 (by omega)) hqd.matrixNegativeBase, ht112, ht113,
        by simpa only [ft.1, Buffers.advance] using hqd.matrixPositive,
        by simpa only [ft.1, Buffers.advance] using hqd.matrixNegative,
        by simpa only [ft.1, Buffers.advance] using hqo.positive,
        by simpa only [ft.1, Buffers.advance] using hqo.negative⟩
    · exact ⟨ht104, ht114, ht115, by simpa only [ft.1, Buffers.advance] using hqd.vectorPositive,
        by simpa only [ft.1, Buffers.advance] using hqd.vectorNegative⟩
  · exact (keepT 140 (by omega)).trans ((keepQ 140 (by omega)).trans (keepA 140 (by omega)))

end Maxwell.Cost.CalibrationMatrix
