import Maxwell.Cost.PhysicalMaterial.Scatter
import Maxwell.Cost.PhysicalMaterial.ScatterMemory

namespace Maxwell.Cost.PhysicalMaterial.Scatter
open Structured RationalAccumulator
set_option maxHeartbeats 1600000

def flatIndex (anchor : Fin 3 → ℕ) (d : Point) (ny nz : ℕ) : ℕ :=
  (coordinate anchor d 0*ny+coordinate anchor d 1)*nz+coordinate anchor d 2

def work : Finset ℕ := {37,292,322,324,325,326}

structure Frame (s t : BitRAMState) : Prop where
  inputHead : t.inputHead = s.inputHead
  randomCursor : t.randomCursor = s.randomCursor
  output : t.output = s.output
  tapes : ∀ i, i = 4 ∨ 10 ≤ i → i ∉ work → t.tapes i = s.tapes i

theorem Frame.refl (s : BitRAMState) : Frame s s := ⟨rfl, rfl, rfl, fun _ _ _ => rfl⟩
theorem Frame.trans {s t u : BitRAMState} (h : Frame s t) (k : Frame t u) : Frame s u :=
  ⟨k.inputHead.trans h.inputHead, k.randomCursor.trans h.randomCursor, k.output.trans h.output,
    fun i hi hn => (k.tapes i hi hn).trans (h.tapes i hi hn)⟩

def PointReady (s : BitRAMState) : Prop :=
  Descriptors.Ready s ∧ Blank s 37 ∧ Blank s 292 ∧ Blank s 322 ∧
    ∀ j : Fin 3, Blank s (324+j.val)

def pointCode (d : Point) : Code := .seq (indexCode d)
  (.seq Dense.writeCode (.call (TapeOps.clear 322)))

def pointBudget (d : Point) (B : ℕ) : ℕ := indexBudget d B+80000*(B+2)^2+6*B+4

/-- Translate one fixed prototype point, compute its actual address, and
scatter the stored strength numerator and denominator to the two dense arrays. -/
theorem point {cells : ℕ} (l : Dense.Layout cells) (nums dens : Vector (List Bool) cells)
    (anchor : Fin 3 → ℕ) (d : Point) (ny nz B num den : ℕ)
    (hl : l.Sized B) (hcount : cells < 2^B) (i : Fin cells)
    (hi : flatIndex anchor d ny nz = i.val)
    (hb : ∀ j, (anchor j).bits.length ≤ B) (hroom : ∀ j, 0 ≤ (anchor j : ℤ)+d j)
    (hnyB : ny.bits.length ≤ B) (hnzB : nz.bits.length ≤ B)
    (hnumB : num.bits.length ≤ addressValue l.width) (hdenB : den.bits.length ≤ addressValue l.width)
    (input : List Bool) (tape : ℕ → Bool) (s : Store) (hr : PointReady s.val)
    (hd : Dense.Stored l nums dens s.val)
    (ha : ∀ j, Word s.val (294+j.val) (anchor j))
    (hny : Word s.val 251 ny) (hnz : Word s.val 252 nz)
    (hnum : Word s.val 276 num) (hden : Word s.val 277 den) :
    ∃ cost t, cost ≤ pointBudget d B ∧ Executes input tape (pointCode d) cost s t ∧
      PointReady t.val ∧
      Dense.Stored l (nums.set i (FixedWidth.bits (addressValue l.width) num.bits))
        (dens.set i (FixedWidth.bits (addressValue l.width) den.bits)) t.val ∧
      Frame s.val t.val ∧ Dense.Outside l s.val t.val := by
  obtain ⟨ic, a, hic, ei, hai, haz, ha292, har, fa⟩ := index_executes d anchor ny nz B hb hroom
    hnyB hnzB input tape s ha hny hnz hr.2.2.2.2 hr.2.2.1 hr.2.2.2.1 hr.1
  have had : Dense.Stored l nums dens a.val :=
    ⟨BankArray.word_of_eq (fa.tapes 300 (by decide)) hd.width,
      BankArray.word_of_eq (fa.tapes 301 (by decide)) hd.clock,
      BankArray.word_of_eq (fa.tapes 320 (by decide)) hd.numBase,
      BankArray.word_of_eq (fa.tapes 321 (by decide)) hd.denBase,
      by simpa only [fa.memory] using hd.nums, by simpa only [fa.memory] using hd.dens⟩
  have hil : i.val.bits.length ≤ B := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr (i.isLt.trans hcount)
  have hai' : Word a.val 322 i.val := by
    change Word a.val 322 (flatIndex anchor d ny nz) at hai
    simpa only [hi] using hai
  obtain ⟨wc, b, hwc, ew, hbr, hb37, hbd, hbm, fb⟩ := Dense.write l nums dens i num den B hl
    hnumB hdenB input tape i.val.bits (addressValue_bits _) hil a har
    (blank_of_eq (fa.tapes 37 (by decide)) hr.2.1) had hai'
    (word_of_eq (fa.tapes 276 (by decide)) hnum) (word_of_eq (fa.tapes 277 (by decide)) hden)
  obtain ⟨io, hio⟩ := hai'
  have hbi : b.val.tapes 322 = BitTape.shifted i.val.bits io :=
    (fb.2.2.2.1 322 (by omega) (by decide)).trans hio
  obtain ⟨t, et, htt, ft⟩ := WordCall.clear 322 input tape i.val.bits io b hbi
  have keep (j : ℕ) (hj : j ≠ 322) : t.val.tapes j = b.val.tapes j := by simp [htt, hj]
  have frame : Frame s.val t.val := by
    refine ⟨ft.2.1.trans (fb.1.trans fa.inputHead),
      ft.2.2.2.1.trans (fb.2.1.trans fa.randomCursor),
      ft.2.2.2.2.1.trans (fb.2.2.1.trans fa.output), ?_⟩
    intro j hj hn
    have hout : j ≠ 37 ∧ j ≠ 322 ∧ j ∉ indexWork := by
      simp only [work, Finset.mem_insert, Finset.mem_singleton, not_or] at hn
      refine ⟨hn.1, hn.2.2.1, ?_⟩
      simp only [indexWork, Finset.mem_insert, Finset.mem_singleton, not_or]
      omega
    exact (keep j hout.2.1).trans ((fb.2.2.2.1 j hj hout.1).trans (fa.tapes j hout.2.2))
  refine ⟨ic+(wc+(6*i.val.bits.length+4)), t, ?_, ei.seq (ew.seq et), ?_, ?_, frame,
    ((Dense.Outside.of_memory l fa.memory).trans (Dense.Outside.of_write l i num den hbm)).trans
      (Dense.Outside.of_memory l ft.2.2.1)⟩
  · dsimp only [pointBudget]
    omega
  · refine ⟨(fun j hj => blank_of_eq (keep j (by omega)) (hbr j hj)),
      blank_of_eq (keep 37 (by decide)) hb37,
      blank_of_eq ((keep 292 (by decide)).trans (fb.2.2.2.1 292 (by omega) (by decide))) ha292,
      ⟨io+i.val.bits.length, by simp [htt]⟩, ?_⟩
    intro j
    exact blank_of_eq ((keep (324+j.val) (by omega)).trans
      (fb.2.2.2.1 (324+j.val) (by omega) (by omega))) (haz j)
  · refine ⟨BankArray.word_of_eq (keep 300 (by decide)) hbd.width,
      BankArray.word_of_eq (keep 301 (by decide)) hbd.clock,
      BankArray.word_of_eq (keep 320 (by decide)) hbd.numBase,
      BankArray.word_of_eq (keep 321 (by decide)) hbd.denBase, ?_, ?_⟩
    · simpa only [ft.2.2.1] using hbd.nums
    · simpa only [ft.2.2.1] using hbd.dens

end Maxwell.Cost.PhysicalMaterial.Scatter
