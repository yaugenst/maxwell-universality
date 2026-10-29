import Maxwell.Cost.CalibrationSource.FactorMultiply

namespace Maxwell.Cost.CalibrationSource.Factor
open Structured CalibrationMatrix Repack
open RationalAccumulator (Blank)
set_option maxHeartbeats 1400000

def words {m : ℕ} (c : Data) (d : ModeRead.Data m) (f : Fin m → ℕ) (a : Fin 2) : Vector (List Bool) m :=
  Vector.ofFn fun i => FixedWidth.bits (addressValue c.width) (f i*d.value i a).bits

@[simp] theorem words_get {m : ℕ} (c : Data) (d : ModeRead.Data m) (f : Fin m → ℕ) (a : Fin 2) (i : Fin m) :
    (words c d f a).get i = FixedWidth.bits (addressValue c.width) (f i*d.value i a).bits := by
  simp [words,Vector.get,Fin.cast]

def stepCode (factor : ℕ) : Code := .seq readCode (.seq (multiplyCode factor) writeCode)

theorem step {m : ℕ} (c : Data) (d : ModeRead.Data m) (f : Fin m → ℕ) (i : Fin m) (B : ℕ)
    (hc : c.Sized B) (hd : d.Sized B) (hsep : c.Separated d)
    (hf : (f i).bits.length ≤ B)
    (hfit : ∀ a, (f i*d.value i a).bits.length ≤ addressValue c.width)
    (out : Fin 2 → Vector (List Bool) m) (input : List Bool) (tape : ℕ → Bool)
    (index : List Bool) (hi : addressValue index = i.val) (hil : index.length ≤ B)
    (s : Store) (hr : Ready s.val (dotValues 0 0)) (h4 : Blank s.val 4)
    (h37 : Blank s.val 37) (hs : Stored c out s.val) (hm : ModeRead.Stored readLayout d s.val)
    (h104 : BankArray.Word s.val 104 index) :
    ∃ cost t, cost ≤ 131000*(B+2)^2 ∧ Executes input tape (stepCode (f i)) cost s t ∧
      Ready t.val (dotValues 0 0) ∧ Blank t.val 4 ∧ Blank t.val 37 ∧
      Stored c (fun a => (out a).set i ((words c d f a).get i)) t.val ∧
      ModeRead.Stored readLayout d t.val ∧ Frame s.val t.val ∧
      OutputOutside c.output m (addressValue c.width) s.val t.val ∧
      BankArray.Word t.val 104 index := by
  obtain ⟨rc,a,hrc,er,ar,a4,a37,am,amem,af,ai⟩ := read d i B hd input tape index hi hil s hr h4 h37 hm h104
  have coefficientBits (j : Fin 2) : (d.value i j).bits.length ≤ B := by
    have hv : (addressValue ((d.words j).get i)).bits.length ≤ ((d.words j).get i).length := by
      rw [Nat.size_eq_bits_len]
      exact Nat.size_le.mpr (Subtraction.addressValue_lt_pow_length _)
    exact hv.trans (((am.arrays j).length i).le.trans hd.2.1)
  obtain ⟨mc,b,hmc,em,br,bmem,bf⟩ := multiply (f i) (d.value i 0) (d.value i 1) B
    hf (coefficientBits 0) (coefficientBits 1) input tape a ar
  have b4 := RationalAccumulator.blank_of_eq (bf.tapes 4 (by omega) (by omega) (by omega) (by omega) (by omega)) a4
  have b37 := RationalAccumulator.blank_of_eq (bf.tapes 37 (by omega) (by omega) (by omega) (by omega) (by omega)) a37
  have bi := BankArray.word_of_eq (bf.tapes 104 (by omega) (by omega) (by omega) (by omega) (by omega)) ai
  have bm := modeStored_of_frame am bf bmem
  have ast := (hs.of_frame af amem).of_frame bf bmem
  obtain ⟨wc,t,hwc,ew,tr,t37,tm,tp,tn,tf⟩ := write input tape c.width index (c.bases 0) (c.bases 1)
    c.clock (out 0) (out 1) i (f i*d.value i 0) (f i*d.value i 1) c.width_nonempty hi c.clock_length
    c.width_positive (hfit 0) (hfit 1) hsep.1 b br b37 ast.width bi (ast.bases 0) (ast.bases 1)
    ast.clock (ast.arrays 0) (ast.arrays 1)
  have wf := Frame.of_row tf
  have allf := (af.trans bf).trans wf
  have t4 : Blank t.val 4 := RationalAccumulator.blank_of_eq
    (tf.2.2.2.1 4 (by omega) (by omega) (by omega) (by omega)) b4
  have source : ModeRead.Stored readLayout d t.val := by
    have keep (j : ℕ) (hj : 510 ≤ j) := tf.2.2.2.1 j (by omega) (by omega) (by omega) (by omega)
    refine ⟨BankArray.word_of_eq (keep 514 (by omega)) bm.width,
      BankArray.word_of_eq (keep 515 (by omega)) bm.clock,?_,
      RationalAccumulator.word_of_eq (keep 512 (by omega)) bm.denominator,?_⟩
    · intro a; apply BankArray.word_of_eq (keep _ _) (bm.bases a)
      fin_cases a <;> decide
    · intro j
      rw [tm]
      apply IncidenceEncoding.represents_write_disjoint _ _ _ i _ (FixedWidth.bits_length _ _) (hsep.2 j 1)
      exact IncidenceEncoding.represents_write_disjoint (bm.arrays j) _ _ i _
        (FixedWidth.bits_length _ _) (hsep.2 j 0)
  have hw := hwc.trans (write_cost_bound c.width index (c.bases 0) (c.bases 1)
    (f i*d.value i 0) (f i*d.value i 1) B hc.1 hil (hc.2.2 0) (hc.2.2 1) hc.2.1)
  refine ⟨rc+(mc+wc),t,by omega,
    er.seq (em.seq ew),tr,t4,t37,?_,source,allf,?_,?_⟩
  · refine ⟨BankArray.word_of_eq (wf.tapes 100 (by omega) (by omega) (by omega) (by omega) (by omega)) ast.width,
      BankArray.word_of_eq (wf.tapes 101 (by omega) (by omega) (by omega) (by omega) (by omega)) ast.clock,?_,?_⟩
    · intro a
      exact BankArray.word_of_eq (wf.tapes _ (by omega) (by omega) (by omega) (by omega) (by omega)) (ast.bases a)
    · intro a; fin_cases a
      · simpa using tp
      · simpa using tn
  · apply (OutputOutside.of_memory (bmem.trans amem)).trans
    exact OutputOutside.of_write i _ _ (FixedWidth.bits_length _ _) (FixedWidth.bits_length _ _) tm
  · exact BankArray.word_of_eq (tf.2.2.2.1 104 (by omega) (by omega) (by omega) (by omega)) bi

end Maxwell.Cost.CalibrationSource.Factor
