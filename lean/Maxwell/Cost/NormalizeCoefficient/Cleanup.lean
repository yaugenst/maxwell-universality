import Maxwell.Cost.RationalAccumulator.Reset

namespace Maxwell.Cost.NormalizeCoefficient

open Structured RationalAccumulator

def cleanupCode : Code := .seq resetCode
  (.seq (.call (TapeOps.clear 33)) (.call (TapeOps.clear 34)))

theorem cleanup (input : List Bool) (tape : ℕ → Bool) (v : ℕ → ℕ)
    (s : Store) (hbank : Bank s.val v) (hready : Scratch s.val 0)
    (h35 : v 35 = 0) (h36 : v 36 = 0) :
    ∃ t : Store, Executes input tape cleanupCode
      (6*((v 30).bits.length+(v 31).bits.length+(v 32).bits.length+
        (v 33).bits.length+(v 34).bits.length)+20) s t ∧
      Bank t.val (fun _ => 0) ∧ Scratch t.val 0 ∧ RationalAccumulator.Frame s.val t.val := by
  obtain ⟨a, ha, hab, har, haf⟩ := reset input tape v s hbank hready
  obtain ⟨b, hb, hbb, hbr, hbf⟩ := clear_bank 33 (by omega) (by omega)
    input tape (resetBank v) 0 a hab har
  obtain ⟨t, ht, htb, htr, htf⟩ := clear_bank 34 (by omega) (by omega)
    input tape (Function.update (resetBank v) 33 0) 0 b hbb hbr
  refine ⟨t, ?_, ?_, htr, (haf.trans hbf).trans htf⟩
  · have he := ha.seq (hb.seq ht)
    simp only [resetBank, Function.update_of_ne (show 33 ≠ 32 by omega),
      Function.update_of_ne (show 33 ≠ 31 by omega), Function.update_of_ne (show 33 ≠ 30 by omega),
      Function.update_of_ne (show 34 ≠ 33 by omega), Function.update_of_ne (show 34 ≠ 32 by omega),
      Function.update_of_ne (show 34 ≠ 31 by omega), Function.update_of_ne (show 34 ≠ 30 by omega)] at he
    convert he using 1 <;> first | rfl | omega
  · intro i hi hi'
    have hh := htb i hi hi'
    interval_cases i <;> simpa [resetBank, h35, h36] using hh

end Maxwell.Cost.NormalizeCoefficient
