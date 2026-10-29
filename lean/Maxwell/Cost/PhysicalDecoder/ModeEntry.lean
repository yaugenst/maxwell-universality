import Maxwell.Cost.PhysicalDecoder.Entry
import Maxwell.Cost.PhysicalDecoder.Sign
import Maxwell.Cost.ModeRead.Value

/-! One actual decoder weight: addressed mode loading, signed conversion,
canonical record emission, and reclamation of all temporary words. -/
namespace Maxwell.Cost.PhysicalDecoder.ModeEntry
open Structured RationalAccumulator

def layout : ModeRead.Layout := ModeRead.retained 359 ![30,31,351]
def work : Finset ℕ := Finset.range 10 ∪ Entry.work ∪ {350,351,358}
def Ready (s : BitRAMState) : Prop := ∀ i ∈ work, Blank s i

structure Frame (s t : BitRAMState) : Prop where
  memory : t.memory = s.memory
  inputHead : t.inputHead = s.inputHead
  randomCursor : t.randomCursor = s.randomCursor
  tapes : ∀ i ∉ work, t.tapes i = s.tapes i

def cleanup : Code := .seq (.call (TapeOps.clear 350))
  (.seq (.call (TapeOps.clear 351)) (.call (TapeOps.clear 358)))
def code (localIndex : ℕ) : Code := .seq (ModeRead.Signed.code layout)
  (.seq Sign.code (.seq (Entry.code localIndex) cleanup))
def costBound (localIndex B : ℕ) : ℕ :=
  50000*(B+2)^2 + 2 + Entry.costBound localIndex B + 12*B+18

theorem layout_valid : layout.Valid := ModeRead.retained_valid 359 ![30,31,351]
  (by decide) (by intro i; fin_cases i <;> decide)
  (by intro i j h; fin_cases i <;> fin_cases j <;> simp_all)
  (by intro i; fin_cases i <;> decide)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
theorem executes {n : ℕ} (d : ModeRead.Data n) (i : Fin n) (rowBase B : ℕ)
    (hd : d.Sized B) (hrow : rowBase.bits.length ≤ B)
    (x : Arithmetic.Data)
    (hx0 : x 0 = (((d.value i 0 : ℕ):ℤ)-d.value i 1).natAbs)
    (hx1 : x 1 = d.denominator) (hv : Arithmetic.Valid x) (hB : Arithmetic.Bounded x B)
    (input : List Bool) (tape : ℕ → Bool) (index : List Bool)
    (hi : addressValue index = i.val) (hil : index.length ≤ B)
    (s : Store) (hs : Ready s.val) (hst : ModeRead.Stored layout d s.val)
    (hindex : BankArray.Word s.val 359 index) (hbase : Word s.val 345 rowBase)
    (hfields : ∀ j : Fin 8, 2 ≤ j.val → Word s.val (350+j.val) (x j)) :
    ∃ cost t, cost ≤ costBound i.val B ∧ Executes input tape (code i.val) cost s t ∧
      t.val.output = (Codec.nat (rowBase+i.val) ++
        Codec.rat (Arithmetic.fraction x (decide (d.value i 0 < d.value i 1)))).reverse ++
          s.val.output ∧ Ready t.val ∧ ModeRead.Stored layout d t.val ∧
      (∀ j : Fin 8, 2 ≤ j.val → Word t.val (350+j.val) (x j)) ∧ Frame s.val t.val := by
  let negative := decide (d.value i 0 < d.value i 1)
  have ready : ModeRead.Ready s.val := fun j hj => hs j (by simp [work, hj])
  have bank : Bank s.val (fun _ => 0) := by
    intro j hj hj'
    apply (zero_word_iff_blank _ _).mpr
    apply hs
    interval_cases j <;> decide
  obtain ⟨cr, r, hcr, er, rr, dr, br, wm, wd, sign, fr⟩ := ModeRead.Signed.executes
    layout layout_valid rfl (by intro j hj; simp only [layout, ModeRead.retained,
      ModeRead.Layout.inputs, Finset.mem_insert, Finset.mem_singleton] at hj; omega)
    (by decide) d i B hd input tape index hi hil s ready hst hindex bank
    (hs 350 (by decide)) (hs 351 (by decide))
  have rz358 : Blank r.val 358 := blank_of_eq (fr.tapes 358 (by decide) (by decide))
    (hs 358 (by decide))
  obtain ⟨a, es, ws, fs, _⟩ := Sign.executes negative input tape r sign rz358
  have same (j : ℕ) (hj : 10 ≤ j) (hn : j∉ModeRead.Signed.changed) (hsign : j≠358) :
      a.val.tapes j = s.val.tapes j :=
    (fs.tapes j (by simpa only [Finset.mem_singleton] using hsign)).trans
      (fr.tapes j (Or.inr hj) hn)
  have ar : PhysicalMaterial.Scatter.Ready a.val := by
    intro j hj
    exact blank_of_eq (fs.tapes j (by simp only [Finset.mem_singleton]; omega)) (rr j hj)
  have ac : Coefficient.Ready x a := by
    refine ⟨?_, ?_⟩
    · intro j
      by_cases h0 : j=0
      · subst j
        exact word_of_eq (fs.tapes 350 (by decide)) (by simpa [hx0] using wm)
      by_cases h1 : j=1
      · subst j
        exact word_of_eq (fs.tapes 351 (by decide)) (by simpa [hx1] using wd)
      have hj : 2 ≤ j.val := by have := j.isLt; omega
      apply word_of_eq (same (350+j.val) (by omega) ?_ (by omega)) (hfields j hj)
      simp only [ModeRead.Signed.changed, Finset.mem_insert, Finset.mem_singleton, not_or]
      omega
    · intro j hj
      have hj358 : j≠358 := by
        simp only [Coefficient.work, Arithmetic.work, PhysicalMaterial.ArithmeticBank.work,
          Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hj
        omega
      apply blank_of_eq (fs.tapes j (by simpa only [Finset.mem_singleton] using hj358))
      by_cases hsmall : j<10
      · exact rr j hsmall
      by_cases hb : 30≤j ∧ j≤36
      · exact (zero_word_iff_blank _ _).mp (br j hb.1 hb.2)
      apply blank_of_eq (fr.tapes j (by omega) ?_) (hs j ?_)
      · simp only [Coefficient.work, Arithmetic.work, PhysicalMaterial.ArithmeticBank.work,
          Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hj
        simp only [ModeRead.Signed.changed, Finset.mem_insert, Finset.mem_singleton, not_or]
        omega
      · exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_union_right _ hj))
  have az343 := blank_of_eq (same 343 (by decide) (by decide) (by decide)) (hs 343 (by decide))
  have az292 := blank_of_eq (same 292 (by decide) (by decide) (by decide)) (hs 292 (by decide))
  obtain ⟨ce, b, hce, ee, bo, bc, bz343, bz292, bready, fe⟩ := Entry.executes i.val
    rowBase x negative B hrow hv hB input tape a
    (word_of_eq (same 345 (by decide) (by decide) (by decide)) hbase) ws ac az343 az292 ar
  obtain ⟨u, eu, zu, fu⟩ := RationalCanonical.clear_word 350 (x 0) input tape b (bc.words 0)
  obtain ⟨v, ev, zv, fv⟩ := RationalCanonical.clear_word 351 (x 1) input tape u
    (word_of_eq (fu.2.2.2.2.2.1 351 (by decide) (by decide)) (bc.words 1))
  have vsign : BankArray.Word v.val 358 [negative] := BankArray.word_of_eq
    ((fv.2.2.2.2.2.1 358 (by decide) (by decide)).trans
      ((fu.2.2.2.2.2.1 358 (by decide) (by decide)).trans (fe.tapes 358 (by decide)))) ws
  obtain ⟨origin, vsg⟩ := vsign
  obtain ⟨t, et, tt, ft⟩ := WordCall.clear 358 input tape [negative] origin v vsg
  have keep (j : ℕ) (h350 : j≠350) (h351 : j≠351) (h358 : j≠358) :
      t.val.tapes j = b.val.tapes j :=
    (ft.2.2.2.2.2.1 j h358 h358).trans
      ((fv.2.2.2.2.2.1 j h351 h351).trans (fu.2.2.2.2.2.1 j h350 h350))
  have preblank : ∀ j ∈ Finset.range 10 ∪ Entry.work, Blank b.val j := by
    intro j hj
    simp only [Entry.work, Finset.mem_union] at hj
    rcases hj with hj | hj | hj
    · exact bready j (Finset.mem_range.mp hj)
    · simp only [Samples.work, Finset.mem_insert, Finset.mem_singleton] at hj
      rcases hj with rfl|rfl|rfl|rfl|rfl|rfl
      · exact bready 0 (by decide)
      · exact bready 1 (by decide)
      · exact bready 2 (by decide)
      · exact bready 3 (by decide)
      · exact bz292
      · exact bz343
    · exact bc.blank j hj
  have frame : Frame s.val t.val := by
    refine ⟨ft.2.2.1.trans (fv.2.2.1.trans (fu.2.2.1.trans
      (fe.memory.trans (fs.memory.trans fr.memory)))),
      ft.2.1.trans (fv.2.1.trans (fu.2.1.trans (fe.inputHead.trans (fs.inputHead.trans fr.inputHead)))),
      ft.2.2.2.1.trans (fv.2.2.2.1.trans (fu.2.2.2.1.trans
        (fe.randomCursor.trans (fs.randomCursor.trans fr.randomCursor)))), ?_⟩
    intro j hj
    have hh : 10≤j ∧ j∉Entry.work ∧ j≠350 ∧ j≠351 ∧ j≠358 := by
      simpa only [work, Finset.mem_union, Finset.mem_range, Finset.mem_insert,
        Finset.mem_singleton, not_or, not_lt, and_assoc] using hj
    apply (keep j hh.2.2.1 hh.2.2.2.1 hh.2.2.2.2).trans
      ((fe.tapes j hh.2.1).trans (same j hh.1 ?_ hh.2.2.2.2))
    have he : j∉Coefficient.work := fun h => hh.2.1 (Finset.mem_union_right _ h)
    simp only [Coefficient.work, Arithmetic.work, PhysicalMaterial.ArithmeticBank.work,
      Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, not_or] at he
    simp only [ModeRead.Signed.changed, Finset.mem_insert, Finset.mem_singleton, not_or]
    omega
  refine ⟨cr+(2+(ce+((6*(x 0).bits.length+4)+((6*(x 1).bits.length+4)+10)))), t,
    by have := hB 0; have := hB 1; unfold costBound; omega,
    er.seq (es.seq (ee.seq (eu.seq (ev.seq et)))), ?_, ?_, ?_, ?_, frame⟩
  · rw [ft.2.2.2.2.1, fv.2.2.2.2.1, fu.2.2.2.2.1, bo, fs.output, fr.output]
  · intro j hj
    simp only [work, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with hj | rfl | rfl | rfl
    · apply blank_of_eq (keep j ?_ ?_ ?_) (preblank j (Finset.mem_union.mpr hj))
      all_goals
        simp only [Entry.work, Coefficient.work, Arithmetic.work, PhysicalMaterial.ArithmeticBank.work,
          Samples.work, Finset.mem_union, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton] at hj
        omega
    · exact blank_of_eq ((ft.2.2.2.2.2.1 350 (by decide) (by decide)).trans
        (fv.2.2.2.2.2.1 350 (by decide) (by decide))) ((zero_word_iff_blank _ _).mp zu)
    · exact blank_of_eq (ft.2.2.2.2.2.1 351 (by decide) (by decide))
        ((zero_word_iff_blank _ _).mp zv)
    · exact ⟨origin+1, by simp [tt]⟩
  · refine ⟨BankArray.word_of_eq (frame.tapes 514 (by decide)) hst.width,
      BankArray.word_of_eq (frame.tapes 515 (by decide)) hst.clock, ?_,
      word_of_eq (frame.tapes 512 (by decide)) hst.denominator, ?_⟩
    · intro a
      apply BankArray.word_of_eq (frame.tapes (layout.base a) _) (hst.bases a)
      fin_cases a <;> decide
    · intro a
      simpa only [frame.memory] using hst.arrays a
  · intro j hj
    apply word_of_eq (frame.tapes (350+j.val) _) (hfields j hj)
    have := j.isLt
    simp only [work, Entry.work, Coefficient.work, Arithmetic.work, PhysicalMaterial.ArithmeticBank.work,
      Samples.work, Finset.mem_union, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton, not_or, not_lt]
    omega

end Maxwell.Cost.PhysicalDecoder.ModeEntry
