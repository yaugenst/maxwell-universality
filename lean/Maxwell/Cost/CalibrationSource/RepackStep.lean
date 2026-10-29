import Maxwell.Cost.CalibrationSource.RepackData

namespace Maxwell.Cost.CalibrationSource.Repack
open Structured CalibrationMatrix
open RationalAccumulator (Blank)
set_option maxHeartbeats 1400000

def stepCode : Code := .seq readCode writeCode

theorem step {m : ℕ} (c : Data) (d : ModeRead.Data m) (i : Fin m) (B : ℕ)
    (hc : c.Sized B) (hd : d.Sized B) (hsep : c.Separated d)
    (hfit : ∀ a, (d.value i a).bits.length ≤ addressValue c.width)
    (out : Fin 2 → Vector (List Bool) m) (input : List Bool) (tape : ℕ → Bool)
    (index : List Bool) (hi : addressValue index = i.val) (hil : index.length ≤ B)
    (s : Store) (hr : Ready s.val (dotValues 0 0)) (h4 : Blank s.val 4)
    (h37 : Blank s.val 37) (hs : Stored c out s.val) (hm : ModeRead.Stored readLayout d s.val)
    (h104 : BankArray.Word s.val 104 index) :
    ∃ cost t, cost ≤ 121000*(B+2)^2 ∧ Executes input tape stepCode cost s t ∧
      Ready t.val (dotValues 0 0) ∧ Blank t.val 4 ∧ Blank t.val 37 ∧
      Stored c (fun a => (out a).set i ((words c d a).get i)) t.val ∧
      ModeRead.Stored readLayout d t.val ∧ Frame s.val t.val ∧
      OutputOutside c.output m (addressValue c.width) s.val t.val ∧
      BankArray.Word t.val 104 index := by
  obtain ⟨rc,a,hrc,er,ar,a4,a37,am,amem,af,ai⟩ := read d i B hd input tape index hi hil s hr h4 h37 hm h104
  have ast := hs.of_frame af amem
  obtain ⟨wc,t,hwc,ew,tr,t37,tm,tp,tn,tf⟩ := write input tape c.width index (c.bases 0) (c.bases 1)
    c.clock (out 0) (out 1) i (d.value i 0) (d.value i 1) c.width_nonempty hi c.clock_length
    c.width_positive (hfit 0) (hfit 1) hsep.1 a ar a37 ast.width ai (ast.bases 0) (ast.bases 1)
    ast.clock (ast.arrays 0) (ast.arrays 1)
  have wf := Frame.of_row tf
  have allf := af.trans wf
  have t4 : Blank t.val 4 := RationalAccumulator.blank_of_eq
    (tf.2.2.2.1 4 (by omega) (by omega) (by omega) (by omega)) a4
  have source : ModeRead.Stored readLayout d t.val := by
    have keep (j : ℕ) (hj : 510 ≤ j) := tf.2.2.2.1 j (by omega) (by omega) (by omega) (by omega)
    refine ⟨BankArray.word_of_eq (keep 514 (by omega)) am.width,
      BankArray.word_of_eq (keep 515 (by omega)) am.clock,?_,
      RationalAccumulator.word_of_eq (keep 512 (by omega)) am.denominator,?_⟩
    · intro a; apply BankArray.word_of_eq (keep _ _) (am.bases a)
      fin_cases a <;> decide
    · intro j
      rw [tm]
      apply IncidenceEncoding.represents_write_disjoint _ _ _ i _ (FixedWidth.bits_length _ _) (hsep.2 j 1)
      exact IncidenceEncoding.represents_write_disjoint (am.arrays j) _ _ i _
        (FixedWidth.bits_length _ _) (hsep.2 j 0)
  have hw := hwc.trans (write_cost_bound c.width index (c.bases 0) (c.bases 1)
    (d.value i 0) (d.value i 1) B hc.1 hil (hc.2.2 0) (hc.2.2 1) hc.2.1)
  refine ⟨rc+wc,t,by omega,
    er.seq ew,tr,t4,t37,?_,source,allf,?_,?_⟩
  · refine ⟨BankArray.word_of_eq (wf.tapes 100 (by omega) (by omega) (by omega) (by omega) (by omega)) ast.width,
      BankArray.word_of_eq (wf.tapes 101 (by omega) (by omega) (by omega) (by omega) (by omega)) ast.clock,?_,?_⟩
    · intro a
      exact BankArray.word_of_eq (wf.tapes _ (by omega) (by omega) (by omega) (by omega) (by omega)) (ast.bases a)
    · intro a; fin_cases a
      · simpa using tp
      · simpa using tn
  · apply (OutputOutside.of_memory amem).trans
    exact OutputOutside.of_write i _ _ (FixedWidth.bits_length _ _) (FixedWidth.bits_length _ _) tm
  · exact BankArray.word_of_eq (tf.2.2.2.1 104 (by omega) (by omega) (by omega) (by omega)) ai

end Maxwell.Cost.CalibrationSource.Repack
