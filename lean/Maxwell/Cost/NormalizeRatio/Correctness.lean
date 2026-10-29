import Maxwell.Cost.NormalizeRatio.Prepare
import Maxwell.Cost.SignedRound

namespace Maxwell.Cost.NormalizeRatio

open Structured RationalAccumulator

def normalized (v : ℕ → ℕ) (negative : Bool) : ℚ :=
  ((if negative then -(v 30 : ℚ) else v 30) / v 31) / ((v 32 : ℚ) / v 33)

theorem normalized_cross_value (v : ℕ → ℕ) (negative : Bool) :
    (if negative then -((v 33 * v 30 : ℕ) : ℚ) else (v 33 * v 30 : ℕ)) /
      (v 32 * v 31 : ℕ) = normalized v negative := by
  cases negative <;> simp [normalized, div_eq_mul_inv] <;> ring

def code : Code := .seq prepareCode
  (.seq (.call (WordTransfer.move 36 1))
    (.seq (.call (TapeOps.copyClear 35 3)) (.seq SignedRound.code (.call (TapeOps.clear 1)))))

def Frame (s t : BitRAMState) : Prop :=
  t.address = s.address ∧ t.inputHead = s.inputHead ∧ t.memory = s.memory ∧
  t.randomCursor = s.randomCursor ∧ t.output = s.output ∧
  (∀ i, 5 ≤ i → (i < 30 ∨ 36 < i) → t.tapes i = s.tapes i) ∧
  (∀ i, 15 ≤ i → (i < 23 ∨ 29 < i) → i ≠ 36 → t.registers i = s.registers i)

theorem Frame.trans {s t u : BitRAMState} (h : Frame s t) (k : Frame t u) : Frame s u := by
  rcases h with ⟨ha, hi, hm, hr, ho, ht, hg⟩
  rcases k with ⟨ka, ki, km, kr, ko, kt, kg⟩
  exact ⟨ka.trans ha, ki.trans hi, km.trans hm, kr.trans hr, ko.trans ho,
    fun i hi hj => (kt i hi hj).trans (ht i hi hj),
    fun i hi hj hk => (kg i hi hj hk).trans (hg i hi hj hk)⟩

theorem frame_of_bank {s t : BitRAMState} (h : RationalAccumulator.Frame s t) : Frame s t := by
  rcases h with ⟨ha, hi, hm, hr, ho, ht, hg⟩
  exact ⟨ha, hi, hm, hr, ho, fun i hi hj => ht i (by omega) hj,
    fun i hi hj _ => hg i hi (by omega) (by omega) (by omega) (by omega)⟩

theorem frame_of_round {s t : BitRAMState} (h : SignedRound.Frame 5 s t) : Frame s t := by
  rcases h with ⟨ha, hi, hm, hr, ho, ht, hg⟩
  exact ⟨ha, hi, hm, hr, ho, fun i hi _ => ht i hi, hg⟩

/-- All scaling, cross products, tape transfers, signed rounding, and
temporary cleanup are part of the fixed program and its quadratic bound. -/
theorem normalizes (input : List Bool) (tape : ℕ → Bool) (v : ℕ → ℕ)
    (B precision : ℕ) (negative : Bool)
    (hbits : ∀ i, 30 ≤ i → i ≤ 34 → (v i).bits.length ≤ B)
    (hqDen : 0 < v 31) (hscaleNum : 0 < v 32) (hscaleDen : 0 < v 33)
    (hpower : v 34 = 2^precision) (hz35 : v 35 = 0) (hz36 : v 36 = 0)
    (s : Store) (hbank : Bank s.val v) (hready : Scratch s.val 0)
    (hfour : Blank s.val 4) (hsign : s.val.registers 35 = negative) :
    ∃ cost, ∃ t : Store, cost ≤ 100000 * (B + 2)^2 ∧
      Executes input tape code cost s t ∧
      SignedRound.Output t.val (Logical.Rounding.nearest precision (normalized v negative)).numerator ∧
      Bank t.val v ∧ Scratch t.val 0 ∧ Frame s.val t.val := by
  obtain ⟨prepCost, p, hpCost, hp, hpb, hpr, hpf⟩ := prepare input tape v B hbits
    hscaleNum hscaleDen (by rw [hpower]; positivity) hz35 hz36 s hbank hready
  obtain ⟨m, hm, hmb, hmr, hmf⟩ := move_to_one 36 (by omega) (by omega)
    input tape (prepared v) p hpb hpr
  let v1 := Function.update (prepared v) 36 0
  obtain ⟨numOrigin, hnum⟩ := hmb 35 (by omega) (by omega)
  obtain ⟨denOrigin, hden⟩ := hmr.2.1
  obtain ⟨ao, hzero⟩ := hmr.1
  obtain ⟨zo, htwo⟩ := hmr.2.2.1
  obtain ⟨yo, hthree⟩ := hmr.2.2.2
  obtain ⟨qo, hfour⟩ := hfour
  have hm4 : m.val.tapes 4 = {BitTape.blank with head := qo} :=
    (hmf.2.2.2.2.2.1 4 (by omega) (Or.inl (by omega))).trans
      ((hpf.2.2.2.2.2.1 4 (by omega) (Or.inl (by omega))).trans hfour)
  have hv135 : v1 35 = prepared v 35 := by simp [v1]
  obtain ⟨copied, hcopy, hcp, hc35, hc3, hcf⟩ := TapeOps.copyClear_to_blank_steps 35 3 (by omega)
    input tape (prepared v 35).bits numOrigin yo m.val m.property
    (by simpa only [← hv135] using hnum) hthree
  let c : Store := Store.ofState copied
  have hec : Executes input tape (.call (TapeOps.copyClear 35 3))
      (8 * (prepared v 35).bits.length + 4) m c :=
    Executes.call _ _ _ _ hcopy (by simp [TapeOps.copyClear, hcp])
  have hcBank : Bank c.val v := by
    intro i hi hi'
    by_cases he35 : i = 35
    · subst i
      rw [hz35, zero_word_iff_blank]
      exact ⟨numOrigin + (prepared v 35).bits.length, hc35⟩
    · have hh := hmb i hi hi'
      have hv1 : v1 i = v i := by
        by_cases he36 : i = 36
        · subst i; simp [v1, hz36]
        · simp [v1, prepared, he35, he36]
      exact word_of_eq (hcf.2.2.2.2.2.1 i he35 (by omega)) (by simpa only [← hv1] using hh)
  have hc0 := (hcf.2.2.2.2.2.1 0 (by omega) (by omega)).trans hzero
  have hc1 := (hcf.2.2.2.2.2.1 1 (by omega) (by omega)).trans hden
  have hc2 := (hcf.2.2.2.2.2.1 2 (by omega) (by omega)).trans htwo
  have hc4 := (hcf.2.2.2.2.2.1 4 (by omega) (by omega)).trans hm4
  have hcSign : c.val.registers 35 = negative :=
    (hcf.2.2.2.2.2.2 35 (by omega) (by omega)).trans
      ((hmf.2.2.2.2.2.2 35 (by omega) (by omega) (by omega) (by omega) (by omega)).trans
        ((hpf.2.2.2.2.2.2 35 (by omega) (by omega) (by omega) (by omega) (by omega)).trans hsign))
  have hnScaled : (v 33 * v 30) * 2^precision = prepared v 35 := by
    simp [prepared, hpower, Nat.mul_comm]
  have hdCross : v 32 * v 31 = prepared v 36 := by simp [prepared]
  obtain ⟨roundCost, r, hrCost, hr, hro, hr1, hr0, hr2, hr3, hrf⟩ :=
    SignedRound.nearest_executes input tape c negative (v 33 * v 30) (v 32 * v 31)
      precision (Nat.mul_pos hscaleNum hqDen) ao denOrigin zo yo qo hc0
      (by simpa only [c, Store.ofState, hdCross] using hc1) hc2
      (by simpa only [c, Store.ofState, hnScaled] using hc3) hc4 hcSign
  have hrBank : Bank r.val v := by
    intro i hi hi'
    exact word_of_eq (hrf.2.2.2.2.2.1 i (by omega)) (hcBank i hi hi')
  have hrReady : Scratch r.val (v 32 * v 31) := ⟨hr0, ⟨denOrigin, hr1⟩, hr2, hr3⟩
  obtain ⟨t, ht, htb, htr, htf⟩ := clear_one input tape v (v 32 * v 31) r hrBank hrReady
  have hcopyFrame : RationalAccumulator.Frame m.val c.val := clone_frame
    (Or.inr (by omega)) (Or.inl (by omega)) (WordTransfer.frame_of_copy hcf)
  refine ⟨prepCost + ((12 * (prepared v 36).bits.length + 11) +
      ((8 * (prepared v 35).bits.length + 4) + (roundCost + (6 * (v 32 * v 31).bits.length + 4)))),
    t, ?_, hp.seq (hm.seq (hec.seq (hr.seq ht))), ?_, htb, htr,
    ((((frame_of_bank hpf).trans (frame_of_bank hmf)).trans (frame_of_bank hcopyFrame)).trans
      (frame_of_round hrf)).trans (frame_of_bank htf)⟩
  · have hb := prepared_bits v B hbits
    rw [hnScaled, hdCross] at hrCost
    rw [hdCross]
    have hrBound : roundCost ≤ 3000 * (5*B+2)^2 := hrCost.trans (by gcongr; omega)
    nlinarith
  · rw [normalized_cross_value] at hro
    obtain ⟨origin, hout, hsg⟩ := hro
    exact ⟨origin,
      (htf.2.2.2.2.2.1 4 (by omega) (Or.inl (by omega))).trans hout,
      (htf.2.2.2.2.2.2 23 (by omega) (by omega) (by omega) (by omega) (by omega)).trans hsg⟩

theorem compiled_run (input : List Bool) (tape : ℕ → Bool) (v : ℕ → ℕ)
    (B precision : ℕ) (negative : Bool)
    (hbits : ∀ i, 30 ≤ i → i ≤ 34 → (v i).bits.length ≤ B)
    (hqDen : 0 < v 31) (hscaleNum : 0 < v 32) (hscaleDen : 0 < v 33)
    (hpower : v 34 = 2^precision) (hz35 : v 35 = 0) (hz36 : v 36 = 0)
    (s : Store) (hbank : Bank s.val v) (hready : Scratch s.val 0)
    (hfour : Blank s.val 4) (hsign : s.val.registers 35 = negative) :
    ∃ t : Store,
      (runPriced (code.compile.next input tape) (100000 * (B + 2)^2 + 1) s.val).finished =
        some (t.place code.size) ∧
      (runPriced (code.compile.next input tape) (100000 * (B + 2)^2 + 1) s.val).instructions ≤
        100000 * (B + 2)^2 ∧
      SignedRound.Output t.val (Logical.Rounding.nearest precision (normalized v negative)).numerator ∧
      Bank t.val v ∧ Scratch t.val 0 ∧ Frame s.val t.val := by
  obtain ⟨cost, t, hc, he, ho, hb, hs, hf⟩ :=
    normalizes input tape v B precision negative hbits hqDen hscaleNum hscaleDen hpower
      hz35 hz36 s hbank hready hfour hsign
  have hr := he.compiled_run (100000 * (B + 2)^2 + 1) (by omega)
  exact ⟨t, hr.1, hr.2 ▸ hc, ho, hb, hs, hf⟩

end Maxwell.Cost.NormalizeRatio
