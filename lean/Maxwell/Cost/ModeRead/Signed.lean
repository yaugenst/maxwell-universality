import Maxwell.Cost.ModeRead
import Maxwell.Cost.IntegerNormSquare.Magnitude

/-! Canonical signed loading from the same pair of addressed mode channels. -/
namespace Maxwell.Cost.ModeRead.Signed
open Structured RationalAccumulator

def values (positive negative : ℕ) (j : ℕ) : ℕ :=
  if j = 30 then positive else if j = 31 then negative else 0

def changed : Finset ℕ := {30,31,32,33,34,35,36,350,351}

structure Frame (s t : BitRAMState) : Prop where
  memory : t.memory = s.memory
  inputHead : t.inputHead = s.inputHead
  randomCursor : t.randomCursor = s.randomCursor
  output : t.output = s.output
  tapes : ∀ j, j = 4 ∨ 10 ≤ j → j ∉ changed → t.tapes j = s.tapes j
  registers : ∀ j, 40 ≤ j → j ≠ 358 → t.registers j = s.registers j

def finishCode : Code := .seq IntegerNormSquare.magnitudeCode
  (.seq (.call (TapeOps.clear 30)) (.seq (.call (TapeOps.clear 31))
    (.seq (.call (WordTransfer.move 34 350)) (Code.atom (.bitAnd 358 23 23)))))

theorem finish (input : List Bool) (tape : ℕ → Bool) (p n : ℕ) (s : Store)
    (hb : Bank s.val (values p n)) (hs : Scratch s.val 0) (h350 : Blank s.val 350) :
    ∃ cost t, cost ≤ 400 * (p.bits.length + n.bits.length + 4) ∧
      Executes input tape finishCode cost s t ∧ Bank t.val (fun _ => 0) ∧
      Scratch t.val 0 ∧ Word t.val 350 ((p : ℤ)-n).natAbs ∧
      t.val.registers 358 = decide (p < n) ∧ Frame s.val t.val ∧
      (∀ j, 4 ≤ j → (j < 30 ∨ 36 < j) → j ≠ 350 → t.val.tapes j = s.val.tapes j) := by
  let v := values p n
  let m := IntegerNormSquare.magnitude p n
  let vm := Function.update v 34 m
  let va := Function.update vm 30 0
  let vb := Function.update va 31 0
  obtain ⟨cm, sm, hcm, em, bm, rm, fm, signm⟩ :=
    IntegerNormSquare.store_magnitude_signed input tape v s hb hs (by simp [v, values])
  have hbm : Bank sm.val vm := by simpa [vm, v, values, m] using bm
  obtain ⟨sa, ea, ba, ra, fa⟩ := clear_bank 30 (by decide) (by decide) input tape vm 0 sm hbm rm
  obtain ⟨sb, eb, bb, rb, fb⟩ := clear_bank 31 (by decide) (by decide) input tape va 0 sa ba ra
  have fm' := fm.trans (DyadicSqrt.frame_of_bank (fa.trans fb))
  have hz350 : Word sb.val 350 0 := (zero_word_iff_blank _ _).mpr
    (blank_of_eq (fm'.2.2.2.2.2.1 350 (by decide) (by omega)) h350)
  have hm34 : Word sb.val 34 m := by simpa [vb, va, vm] using bb 34 (by decide) (by decide)
  obtain ⟨sc, ec, z34, w350, fc⟩ := RationalCanonical.move_word 34 350 m
    (by decide) input tape sb hm34 hz350
  let t := Store.ofState (sc.val.setRegister 358 (sc.val.registers 23 && sc.val.registers 23))
  have et := Executes.bitAnd input tape sc 358 23 23
  have signc : sc.val.registers 23 = SignedDifference.sign p.bits n.bits := by
    exact (fc.2.2.2.2.2.2 23 (by decide) (by decide) (by decide) (by decide)).trans
      ((fb.2.2.2.2.2.2 23 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        ((fa.2.2.2.2.2.2 23 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
          (by simpa [v, values] using signm)))
  have signs : SignedDifference.sign p.bits n.bits = decide (p<n) := by
    apply Bool.eq_iff_iff.mpr
    simp only [SignedDifference.sign_iff, address_bits, decide_eq_true_eq]
  have same (j : ℕ) (hj : 4 ≤ j) (hbank : j<30 ∨ 36<j) (hout : j ≠ 350) :
      t.val.tapes j = s.val.tapes j :=
    (fc.2.2.2.2.2.1 j (by omega) hout).trans (fm'.2.2.2.2.2.1 j hj hbank)
  refine ⟨cm + ((6*(vm 30).bits.length+4) + ((6*(va 31).bits.length+4) +
    ((12*m.bits.length+11)+2))), t, ?_, em.seq (ea.seq (eb.seq (ec.seq et))), ?_, ?_,
    w350, ?_, ?_, same⟩
  · have hm := IntegerNormSquare.magnitude_bits_length_le p n
    simp [v, values] at hcm
    simp [vm, va, v, values]
    dsimp [m]
    omega
  · intro j hj hj'
    by_cases he : j = 34
    · subst j; exact z34
    · have hv : vb j = 0 := by
        simp [vb, va, vm, v, Function.update_apply, values, he]
        intro h31 h30
        simp [h30, h31]
      have hword := bb j hj hj'
      change Word sb.val j (vb j) at hword
      rw [hv] at hword
      exact word_of_eq (fc.2.2.2.2.2.1 j he (by omega)) hword
  · exact ⟨blank_of_eq (fc.2.2.2.2.2.1 0 (by decide) (by decide)) rb.1,
      word_of_eq (fc.2.2.2.2.2.1 1 (by decide) (by decide)) rb.2.1,
      blank_of_eq (fc.2.2.2.2.2.1 2 (by decide) (by decide)) rb.2.2.1,
      blank_of_eq (fc.2.2.2.2.2.1 3 (by decide) (by decide)) rb.2.2.2⟩
  · simp [t, Store.ofState, BitRAMState.setRegister, signc, signs]
  · refine ⟨fc.2.2.1.trans fm'.2.2.1, fc.2.1.trans fm'.2.1,
      fc.2.2.2.1.trans fm'.2.2.2.1, fc.2.2.2.2.1.trans fm'.2.2.2.2.1, ?_, ?_⟩
    · intro j hj hn
      have hne : j≠350 ∧ (j<30 ∨ 36<j) := by simp only [changed, Finset.mem_insert,
        Finset.mem_singleton, not_or] at hn; omega
      exact same j (by omega) hne.2 hne.1
    · intro j hj hn
      change (Function.update sc.val.registers 358 _) j = _
      rw [Function.update_of_ne hn]
      exact (fc.2.2.2.2.2.2 j (by omega) (by omega) (by omega) (by omega)).trans
        (fm'.2.2.2.2.2.2 j (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega))

def code (l : Layout) : Code := .seq (ModeRead.code l) finishCode

private theorem bits_value_length (word : List Bool) :
    (addressValue word).bits.length ≤ word.length := by
  obtain ⟨core, n, he, hc⟩ := TapeOps.trailing_zero_decomposition word
  rw [he, TapeOps.addressValue_append_zeros, TapeOps.canonicalBits_bits hc]
  simp

theorem executes {n : ℕ} (l : Layout) (hl : l.Valid)
    (hout : l.output = ![30,31,351])
    (hinputs : ∀ j ∈ l.inputs, 37 ≤ j) (h350input : 350 ∉ l.inputs)
    (d : Data n) (i : Fin n) (B : ℕ) (hd : d.Sized B)
    (input : List Bool) (tape : ℕ → Bool) (index : List Bool)
    (hi : addressValue index = i.val) (hil : index.length ≤ B) (s : Store)
    (hs : Ready s.val) (hst : Stored l d s.val) (hindex : BankArray.Word s.val l.index index)
    (hb : Bank s.val (fun _ => 0)) (h350 : Blank s.val 350) (h351 : Blank s.val 351) :
    ∃ cost t, cost ≤ 50000*(B+2)^2 ∧ Executes input tape (code l) cost s t ∧
      Ready t.val ∧ Stored l d t.val ∧ Bank t.val (fun _ => 0) ∧
      Word t.val 350 (((d.value i 0 : ℕ) : ℤ)-d.value i 1).natAbs ∧
      Word t.val 351 d.denominator ∧
      t.val.registers 358 = decide (d.value i 0 < d.value i 1) ∧ Frame s.val t.val := by
  have hz : ∀ a, Blank s.val (l.output a) := by
    intro a
    rw [hout]
    fin_cases a
    · exact (zero_word_iff_blank _ _).mp (hb 30 (by decide) (by decide))
    · exact (zero_word_iff_blank _ _).mp (hb 31 (by decide) (by decide))
    · exact h351
  obtain ⟨cr, sr, hcr, er, rr, str, wp, wn, wd, fr⟩ :=
    ModeRead.executes l hl d i B hd input tape index hi hil s hs hst hindex hz
  simp only [hout] at wp wn wd
  change Word sr.val 30 (d.value i 0) at wp
  change Word sr.val 31 (d.value i 1) at wn
  change Word sr.val 351 d.denominator at wd
  have br : Bank sr.val (values (d.value i 0) (d.value i 1)) := by
    intro j hj hj'
    by_cases h30 : j=30
    · subst j; simpa [values] using wp
    by_cases h31 : j=31
    · subst j; simpa [values] using wn
    simp only [values, h30, h31, ↓reduceIte]
    apply word_of_eq (fr.tapes j (by omega) _) (hb j hj hj')
    simp only [Layout.changed, hout, Finset.mem_image, Finset.mem_univ, true_and,
      not_exists, Fin.forall_fin_succ]
    norm_num
    omega
  have hr : Scratch sr.val 0 := ⟨rr 0 (by decide),
    (zero_word_iff_blank _ _).mpr (rr 1 (by decide)), rr 2 (by decide), rr 3 (by decide)⟩
  have hr350 : Blank sr.val 350 := blank_of_eq
    (fr.tapes 350 (by decide) (by simp [Layout.changed, hout, Fin.forall_fin_succ])) h350
  obtain ⟨cf, t, hcf, ef, bt, rt, wm, sg, ff, same⟩ :=
    finish input tape (d.value i 0) (d.value i 1) sr br hr hr350
  have frame : Frame s.val t.val := by
    refine ⟨ff.memory.trans fr.memory, ff.inputHead.trans fr.inputHead,
      ff.randomCursor.trans fr.randomCursor, ff.output.trans fr.output, ?_, ?_⟩
    · intro j hj hn
      apply (ff.tapes j hj hn).trans (fr.tapes j hj _)
      have hh : j≠30 ∧ j≠31 ∧ j≠351 := by simp only [changed, Finset.mem_insert,
        Finset.mem_singleton, not_or] at hn; omega
      simp [Layout.changed, hout, Fin.forall_fin_succ]
      omega
    · intro j hj hn
      exact (ff.registers j hj hn).trans (fr.registers j (by omega))
  have sameInput (j : ℕ) (hj : j∈l.inputs) : t.val.tapes j = s.val.tapes j := by
    apply frame.tapes j (Or.inr (hl.1 j hj))
    have hj37 := hinputs j hj
    have hj350 : j≠350 := by intro he; exact h350input (he ▸ hj)
    have hj351 : j≠351 := by simpa [hout] using l.input_ne_output hl hj 2
    simp only [changed, Finset.mem_insert, Finset.mem_singleton, not_or]
    omega
  refine ⟨cr+cf, t, ?_, er.seq ef, ?_, ?_, bt, wm,
    word_of_eq (same 351 (by decide) (by omega) (by decide)) wd, sg, frame⟩
  · have hlen (a : Fin 2) : (d.value i a).bits.length ≤ B :=
      (bits_value_length _).trans ((hst.arrays a).length i ▸ hd.2.1)
    have h0 := hlen 0
    have h1 := hlen 1
    nlinarith
  · intro j hj
    by_cases hj4 : j<4
    · interval_cases j
      · exact rt.1
      · exact (zero_word_iff_blank _ _).mp rt.2.1
      · exact rt.2.2.1
      · exact rt.2.2.2
    · exact blank_of_eq (same j (by omega) (by omega) (by omega)) (rr j hj)
  · refine ⟨BankArray.word_of_eq (sameInput _ (by simp [Layout.inputs])) hst.width,
      BankArray.word_of_eq (sameInput _ (by simp [Layout.inputs])) hst.clock, ?_,
      word_of_eq (sameInput _ (by simp [Layout.inputs])) hst.denominator, ?_⟩
    · intro a
      apply BankArray.word_of_eq (sameInput _ _) (hst.bases a)
      fin_cases a <;> simp [Layout.base, Layout.inputs]
    · intro a
      simpa only [frame.memory] using hst.arrays a

theorem zero_sign (p n : ℕ) (hz : ((p:ℤ)-n).natAbs = 0) : decide (p<n) = false := by
  have hzero : (p:ℤ)-n = 0 := Int.natAbs_eq_zero.mp hz
  have he : p=n := by omega
  simp [he]

end Maxwell.Cost.ModeRead.Signed
