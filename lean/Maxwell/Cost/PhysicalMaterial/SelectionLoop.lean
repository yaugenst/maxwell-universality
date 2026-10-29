import Maxwell.Cost.PhysicalMaterial.SelectionRow

namespace Maxwell.Cost.PhysicalMaterial.Descriptors
open Structured RationalAccumulator
set_option maxHeartbeats 1800000

 def scanWork : Finset ℕ := rowWork ∪ {303}

def Invariant {n : ℕ} (d : Data n) (cell : Fin 3 → ℕ) (hit : Fin n → Bool)
    (B : ℕ) (initial : BitRAMState) (remaining : ℕ) (s : Store) : Prop :=
  remaining ≤ n ∧ ∃ index : List Bool,
    addressValue index = n-remaining ∧ index.length ≤ B ∧ BankArray.Word s.val 302 index ∧
    Ready s.val ∧ Stored d s.val ∧ Bank s.val (fun _ => 0) ∧ Cell s.val cell ∧ TestReady s.val ∧
    Pair s.val (selectedThrough d hit (n-remaining)) ∧ Frame scanWork initial s.val

private theorem stable {n : ℕ} (d : Data n) (cell : Fin 3 → ℕ) (hit : Fin n → Bool)
    (B : ℕ) (initial : BitRAMState) (remaining : ℕ) (s t : Store)
    (hf : CountedShifted.Frame 303 s t) (hs : Invariant d cell hit B initial remaining s) :
    Invariant d cell hit B initial remaining t := by
  obtain ⟨hr, index, hi, hil, hindex, hready, hd, hb, hc, ht, hp, hframe⟩ := hs
  have keep := hf.2.2.2.2.2.1
  have frame : Frame scanWork s.val t.val :=
    ⟨hf.2.2.1, hf.2.1, hf.2.2.2.1, hf.2.2.2.2.1, fun j _ hj => keep j (by
      intro he; subst j; exact hj (by simp [scanWork]))⟩
  refine ⟨hr, index, hi, hil, BankArray.word_of_eq (keep 302 (by decide)) hindex,
    (fun j hj => blank_of_eq (keep j (by omega)) (hready j hj)), ?_, ?_, ?_, ?_,
    ⟨word_of_eq (keep 272 (by decide)) hp.1, word_of_eq (keep 273 (by decide)) hp.2⟩,
    hframe.trans frame⟩
  · refine ⟨BankArray.word_of_eq (keep 300 (by decide)) hd.width,
      BankArray.word_of_eq (keep 301 (by decide)) hd.clock, ?_, ?_⟩
    · intro j
      exact BankArray.word_of_eq (keep (baseTape j) (by simp only [baseTape]; omega)) (hd.bases j)
    · intro j
      simpa only [hf.2.2.1] using hd.arrays j
  · intro j
    exact word_of_eq (keep (targetTape j) (by have := targetTape_bounds j; omega)) (hb j)
  · intro j
    exact word_of_eq (keep (240+j.val) (by omega)) (hc j)
  · exact ⟨blank_of_eq (keep 290 (by decide)) ht.1,
      blank_of_eq (keep 291 (by decide)) ht.2.1,
      blank_of_eq (keep 292 (by decide)) ht.2.2⟩

def scanCode (test : Code) : Code := .seq (CountedShifted.code 303 (rowCode test))
  (.seq (.call (TapeOps.clear 303)) (.call (TapeOps.clear 302)))

def scanBudget (n B testBudget : ℕ) : ℕ :=
  (n+1)*(13*B+15)+n*rowBudget B testBudget+12*B+8

/-- The actual finite countdown visits every stored descriptor, then reclaims
both its index and count tapes. Its only retained result is the selected pair. -/
theorem scan {n : ℕ} (d : Data n) (cell : Fin 3 → ℕ) (hit : Fin n → Bool)
    (test : Code) (testBudget B : ℕ) (hd : d.Sized B) (hn : n < 2^B)
    (input : List Bool) (tape : ℕ → Bool) (hTest : TestCorrect d cell hit test testBudget input tape)
    (index count : List Bool) (hi : addressValue index = 0) (hcount : addressValue count = n)
    (hil : index.length ≤ B) (hcl : count.length ≤ B) (origin : ℤ) (s : Store)
    (hs : Ready s.val) (hdata : Stored d s.val) (hindex : BankArray.Word s.val 302 index)
    (hcounter : s.val.tapes 303 = BitTape.shifted count origin)
    (hbank : Bank s.val (fun _ => 0)) (hcell : Cell s.val cell) (htest : TestReady s.val)
    (hpair : Pair s.val (0, 1)) :
    ∃ cost t, cost ≤ scanBudget n B testBudget ∧ Executes input tape (scanCode test) cost s t ∧
      Ready t.val ∧ Stored d t.val ∧ Bank t.val (fun _ => 0) ∧ Cell t.val cell ∧ TestReady t.val ∧
      Pair t.val (selectedThrough d hit n) ∧ Blank t.val 302 ∧ Blank t.val 303 ∧
      Frame scanWork s.val t.val := by
  have hB : 0 < B := lt_of_lt_of_le d.width_nonempty hd.1
  have bits (j : Fin n) : (strengthPair d j).1.bits.length ≤ B ∧
      (strengthPair d j).2.bits.length ≤ B :=
    ⟨(value_bits d j 3 s.val hdata).trans hd.2.1, (value_bits d j 4 s.val hdata).trans hd.2.1⟩
  let inv := Invariant d cell hit B s.val
  have body : ∀ r xs u, inv (r+1) u → u.val.tapes 303 = BitTape.shifted xs origin →
      addressValue xs = r → ∃ bodyCost t, Executes input tape (rowCode test) bodyCost u t ∧
        inv r t ∧ t.val.tapes 303 = BitTape.shifted xs origin ∧ bodyCost ≤ rowBudget B testBudget := by
    intro r xs u hu hcounter _
    obtain ⟨hr, index, hi, hil, hui, hur, hud, hub, huc, hut, hup, huf⟩ := hu
    let i : Fin n := ⟨n-(r+1), by omega⟩
    obtain ⟨cost, t, hcost, he, htr, htd, htb, htc, htt, htp, hti, htf⟩ :=
      row d cell hit test testBudget B hd input tape hTest i index hi hil
        (selectedThrough d hit i.val) (selectedThrough_bits d hit B hB bits i.val)
        u hur hud hui hub huc hut hup
    have hnext : n-r = i.val+1 := by dsimp only [i]; omega
    have hlen : (Increment.bits index).length ≤ B := BankArray.increment_length_bound index B hil
      (by rw [hi]; dsimp only [i] at hnext; omega)
    have hf : Frame scanWork u.val t.val := htf.mono Finset.subset_union_left
    refine ⟨cost, t, he, ⟨by omega, Increment.bits index, ?_, hlen, hti,
      htr, htd, htb, htc, htt, ?_, huf.trans hf⟩,
      (htf.tapes 303 (by omega) (by decide)).trans hcounter, hcost⟩
    · rw [Increment.bits_value, hi]
      dsimp only [i] at hnext
      omega
    · rw [hnext, selectedThrough_step]
      exact htp
  have initial : inv n s := by
    refine ⟨le_rfl, index, by simpa using hi, hil, hindex, hs, hdata, hbank, hcell, htest, ?_, .refl _ _⟩
    simpa using hpair
  obtain ⟨cost, a, finalCount, ea, hai, hac, hal, _, hab⟩ := CountedShifted.executes
    303 origin (rowCode test) input tape inv (fun _ => rowBudget B testBudget)
    (stable d cell hit B s.val) body n count s hcount hcounter initial
  obtain ⟨_, finalIndex, _, hfil, ⟨io, hio⟩, har, had, hav, hacell, hat, hap, haf⟩ := hai
  obtain ⟨b, eb, hbt, fb⟩ := WordCall.clear 303 input tape finalCount origin a hac
  have hbi : b.val.tapes 302 = BitTape.shifted finalIndex io := by simpa [hbt] using hio
  obtain ⟨t, et, htt, ft⟩ := WordCall.clear 302 input tape finalIndex io b hbi
  have keep (j : ℕ) (h302 : j ≠ 302) (h303 : j ≠ 303) : t.val.tapes j = a.val.tapes j := by
    simp [htt, hbt, h302, h303]
  have frame : Frame scanWork a.val t.val := by
    refine ⟨ft.2.2.1.trans fb.2.2.1, ft.2.1.trans fb.2.1,
      ft.2.2.2.1.trans fb.2.2.2.1, ft.2.2.2.2.1.trans fb.2.2.2.2.1, ?_⟩
    intro j _ hj
    apply keep j
    · intro heq; subst j; exact hj (by decide)
    · intro heq; subst j; exact hj (by decide)
  refine ⟨cost+((6*finalCount.length+4)+(6*finalIndex.length+4)), t, ?_, ea.seq (eb.seq et),
    (fun j hj => blank_of_eq (keep j (by omega) (by omega)) (har j hj)), ?_, ?_, ?_, ?_,
    ⟨word_of_eq (keep 272 (by decide) (by decide)) hap.1,
      word_of_eq (keep 273 (by decide) (by decide)) hap.2⟩,
    ⟨io+finalIndex.length, by simp [htt]⟩,
    ⟨origin+finalCount.length, by simp [htt, hbt]⟩, haf.trans frame⟩
  · simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at hab
    have hc : finalCount.length ≤ B := hal.le.trans hcl
    have hcounter : (n+1)*(13*count.length+15) ≤ (n+1)*(13*B+15) := by gcongr
    dsimp only [scanBudget]
    omega
  · refine ⟨BankArray.word_of_eq (keep 300 (by decide) (by decide)) had.width,
      BankArray.word_of_eq (keep 301 (by decide) (by decide)) had.clock, ?_, ?_⟩
    · intro j
      exact BankArray.word_of_eq (keep (baseTape j) (by simp only [baseTape]; omega)
        (by simp only [baseTape]; omega)) (had.bases j)
    · intro j
      simpa only [frame.memory] using had.arrays j
  · intro j
    exact word_of_eq (keep (targetTape j) (by have := targetTape_bounds j; omega)
      (by have := targetTape_bounds j; omega)) (hav j)
  · intro j
    exact word_of_eq (keep (240+j.val) (by omega) (by omega)) (hacell j)
  · exact ⟨blank_of_eq (keep 290 (by decide) (by decide)) hat.1,
      blank_of_eq (keep 291 (by decide) (by decide)) hat.2.1,
      blank_of_eq (keep 292 (by decide) (by decide)) hat.2.2⟩

end Maxwell.Cost.PhysicalMaterial.Descriptors
