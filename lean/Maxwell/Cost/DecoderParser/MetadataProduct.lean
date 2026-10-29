import Maxwell.Cost.DecoderParser.LoadMessages
import Maxwell.Cost.PadWord
import Maxwell.Cost.StoredAdd
import Maxwell.Cost.StoredProduct
import Maxwell.Cost.IndexedAddress

namespace Maxwell.Cost.DecoderParser.MetadataProduct
open Structured

structure Frame (work : Finset ℕ) (s t : BitRAMState) : Prop where
  address : t.address = s.address
  inputHead : t.inputHead = s.inputHead
  memory : t.memory = s.memory
  randomCursor : t.randomCursor = s.randomCursor
  output : t.output = s.output
  tapes : ∀ i ∉ work, t.tapes i = s.tapes i

theorem Frame.trans {work : Finset ℕ} {s t u : BitRAMState}
    (h : Frame work s t) (k : Frame work t u) : Frame work s u :=
  ⟨k.address.trans h.address, k.inputHead.trans h.inputHead, k.memory.trans h.memory,
    k.randomCursor.trans h.randomCursor, k.output.trans h.output,
    fun i hi => (k.tapes i hi).trans (h.tapes i hi)⟩

theorem Frame.mono {a b : Finset ℕ} {s t : BitRAMState} (h : Frame a s t)
    (hab : a ⊆ b) : Frame b s t :=
  ⟨h.address, h.inputHead, h.memory, h.randomCursor, h.output,
    fun i hi => h.tapes i (fun hh => hi (hab hh))⟩

def work : Finset ℕ := {0, 1, 2, 3, 60, 64}

private theorem clone_steps (work : Finset ℕ) (source target : ℕ) (htarget : target ∈ work) (hne : source ≠ target)
    (input : List Bool) (tape : ℕ → Bool) (bits : List Bool) (so targetOrigin : ℤ) (s : Store)
    (hs : s.val.tapes source = BitTape.shifted bits so)
    (ht : s.val.tapes target = {BitTape.blank with head := targetOrigin}) :
    ∃ t, Executes input tape (.call (WordTransfer.clone source target)) (15 * bits.length + 17) s t ∧
      t.val.tapes target = BitTape.shifted bits targetOrigin ∧ Frame work s.val t.val := by
  obtain ⟨t, he, hp, hsource, htarget', hf⟩ :=
    WordTransfer.clone_steps source target hne input tape bits so targetOrigin s.val s.property hs ht
  refine ⟨Store.ofState t, Executes.call _ s t _ he (by simp [WordTransfer.clone, hp, Copy.program, Rewind.program, BitRAMInstruction.relocate]), htarget',
    hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2.1, ?_⟩
  intro i hi
  by_cases his : i = source
  · subst i
    exact hsource.trans hs.symm
  · exact hf.2.2.2.2.2.1 i his (fun h => hi (h ▸ htarget))

private theorem pad_steps (work : Finset ℕ) (target : ℕ) (htarget : target ∈ work)
    (input : List Bool) (tape : ℕ → Bool) (bits : List Bool) (origin : ℤ) (s : Store)
    (ht : s.val.tapes target = BitTape.shifted bits origin) :
    ∃ cost t, cost ≤ 6 ∧ Executes input tape (.call (PadWord.program target)) cost s t ∧
      t.val.tapes target = BitTape.shifted (PadWord.bits bits) origin ∧ Frame work s.val t.val := by
  obtain ⟨cost, hc, he, ht', hf⟩ := PadWord.simulation target origin input tape bits s.val s.property ht
  exact ⟨cost + 1, Store.ofState (PadWord.finish target s.val bits), by omega,
    Executes.call _ s _ _ he (by simp [PadWord.program, PadWord.finish]), ht',
    hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2.1,
    fun i hi => hf.2.2.2.2.2.1 i (fun h => hi (h ▸ htarget)) (fun h => hi (h ▸ htarget))⟩

private theorem clear_steps (work : Finset ℕ) (target : ℕ) (htarget : target ∈ work)
    (input : List Bool) (tape : ℕ → Bool) (bits : List Bool) (origin : ℤ) (s : Store)
    (ht : s.val.tapes target = BitTape.shifted bits origin) :
    ∃ t, Executes input tape (.call (TapeOps.clear target)) (6 * bits.length + 4) s t ∧
      t.val.tapes target = {BitTape.blank with head := origin + bits.length} ∧ Frame work s.val t.val := by
  obtain ⟨t, he, hp, ht', hf⟩ := TapeOps.clear_steps target input tape bits origin s.val s.property ht
  exact ⟨Store.ofState t, Executes.call _ s _ _ he (by simp [TapeOps.clear, hp]), ht',
    hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2.1,
    fun i hi => hf.2.2.2.2.2.1 i (fun h => hi (h ▸ htarget)) (fun h => hi (h ▸ htarget))⟩

private theorem move_steps (work : Finset ℕ) (source target : ℕ) (hsource : source ∈ work) (htarget : target ∈ work)
    (hne : source ≠ target) (input : List Bool) (tape : ℕ → Bool) (bits : List Bool)
    (so targetOrigin : ℤ) (s : Store)
    (hs : s.val.tapes source = BitTape.shifted bits so)
    (ht : s.val.tapes target = {BitTape.blank with head := targetOrigin}) :
    ∃ t, Executes input tape (.call (WordTransfer.move source target)) (12 * bits.length + 11) s t ∧
      t.val.tapes source = {BitTape.blank with head := so + bits.length} ∧
      t.val.tapes target = BitTape.shifted bits targetOrigin ∧ Frame work s.val t.val := by
  obtain ⟨t, he, hp, hsource', htarget', hf⟩ :=
    WordTransfer.move_steps source target hne input tape bits so targetOrigin s.val s.property hs ht
  exact ⟨Store.ofState t, Executes.call _ s _ _ he (by simp [WordTransfer.move, hp, TapeOps.copyClear, Rewind.program, BitRAMInstruction.relocate]), hsource', htarget',
    hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2.1,
    fun i hi => hf.2.2.2.2.2.1 i (fun h => hi (h ▸ hsource)) (fun h => hi (h ▸ htarget))⟩

private theorem increment_steps (input : List Bool) (tape : ℕ → Bool) (bits : List Bool)
    (origin : ℤ) (s : Store) (ht : s.val.tapes 64 = BitTape.shifted bits origin) :
    ∃ cost t, cost ≤ 12 * bits.length + 18 ∧
      Executes input tape (.seq (.call (Increment.program 64)) (.call (Rewind.program 64))) cost s t ∧
      t.val.tapes 64 = BitTape.shifted (Increment.bits bits) origin ∧ Frame {64} s.val t.val := by
  obtain ⟨cost, r, hc, he, hp, ht', hf⟩ := Increment.simulation 64 input tape bits origin s.val s.property ht
  let r' := Store.ofState r
  have hi := Executes.call (Increment.program 64) s r _ he (by simp [Increment.program, hp])
  have hr := WordTransfer.rewind_shifted 64 origin input tape (Increment.bits bits) r'.val r'.property ht'
  let t := Rewind.finishAt 64 origin r'.val
  have hre := Executes.call (Rewind.program 64) r' t _ hr.1 (by simp [t, Rewind.program, Rewind.finishAt])
  refine ⟨(cost + 1) + (4 * (Increment.bits bits).length + 6), Store.ofState t,
    by have hh := Increment.bits_length_le bits; omega, hi.seq hre, hr.2, ?_⟩
  refine ⟨hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2.1, ?_⟩
  intro i hiw
  have hi64 : i ≠ 64 := by simpa using hiw
  simpa [t, Rewind.finishAt, hi64, Store.ofState, r'] using hf.2.2.2.2.2.1 i hi64

/-- Add the two metadata words using the stored binary adder, then charge
an actual increment for the sign bit. -/
def widthCode : Code :=
  .seq (.call (WordTransfer.clone 41 1))
  (.seq (.call (WordTransfer.clone 42 64))
  (.seq (.call (PadWord.program 1))
  (.seq (.call (PadWord.program 64))
  (.seq (.call (StoredAdd.program 64))
  (.seq (.seq (.call (Increment.program 64)) (.call (Rewind.program 64)))
  (.seq (.call (TapeOps.clear 1)) (.call (WordTransfer.move 64 1))))))))

def widthBits (integerBits fractionalBits : ℕ) : List Bool :=
  Increment.bits (integerBits + fractionalBits).bits

theorem widthBits_value (i f : ℕ) : addressValue (widthBits i f) = 1 + i + f := by
  simp [widthBits, Increment.bits_value, addressValue_bits]
  omega

theorem widthBits_nonempty (i f : ℕ) : 0 < (widthBits i f).length := by
  by_contra hn
  have he : widthBits i f = [] := List.length_eq_zero_iff.mp (by omega)
  have hv := widthBits_value i f
  rw [he] at hv
  simp [addressValue] at hv
  omega

theorem widthBits_length (i f : ℕ) : (widthBits i f).length ≤ i.bits.length + f.bits.length + 2 := by
  have hs := IndexedAddress.sum_length_le i.bits f.bits
  simp only [addressValue_bits] at hs
  exact (Increment.bits_length_le _).trans (by omega)

theorem width_steps (input : List Bool) (tape : ℕ → Bool) (i f : ℕ) (s : Store)
    (h0 : s.val.tapes 0 = BitTape.blank) (h1 : s.val.tapes 1 = BitTape.blank)
    (h2 : s.val.tapes 2 = BitTape.blank) (h64 : s.val.tapes 64 = BitTape.blank)
    (hi : s.val.tapes 41 = BitTape.ofList i.bits) (hf : s.val.tapes 42 = BitTape.ofList f.bits) :
    ∃ cost t ao wo zo so,
      cost ≤ 300 * (i.bits.length + f.bits.length + 4) ∧
      Executes input tape widthCode cost s t ∧
      t.val.tapes 0 = {BitTape.blank with head := ao} ∧
      t.val.tapes 1 = BitTape.shifted (widthBits i f) wo ∧
      t.val.tapes 2 = {BitTape.blank with head := zo} ∧
      t.val.tapes 64 = {BitTape.blank with head := so} ∧
      Frame {0, 1, 2, 64} s.val t.val := by
  obtain ⟨a, ea, ha1, fa⟩ := clone_steps {1} 41 1 (by simp) (by decide)
    input tape i.bits 0 0 s (by simpa [BitTape.shifted, BitTape.ofList] using hi) h1
  have ha64 : a.val.tapes 64 = BitTape.blank := (fa.tapes 64 (by simp)).trans h64
  have haf : a.val.tapes 42 = BitTape.ofList f.bits := (fa.tapes 42 (by simp)).trans hf
  obtain ⟨b, eb, hb64, fb⟩ := clone_steps {64} 42 64 (by simp) (by decide)
    input tape f.bits 0 0 a (by simpa [BitTape.shifted, BitTape.ofList] using haf) ha64
  have hb1 : b.val.tapes 1 = BitTape.shifted i.bits 0 := (fb.tapes 1 (by simp)).trans ha1
  obtain ⟨pc1, c, hpc1, ec, hc1, fc⟩ := pad_steps {1} 1 (by simp) input tape i.bits 0 b hb1
  have hc64 : c.val.tapes 64 = BitTape.shifted f.bits 0 := (fc.tapes 64 (by simp)).trans hb64
  obtain ⟨pc2, d, hpc2, ed, hd64, fd⟩ := pad_steps {64} 64 (by simp) input tape f.bits 0 c hc64
  let A := PadWord.bits i.bits
  let F := PadWord.bits f.bits
  let P := (i + f).bits
  have hfd : Frame {1, 64} s.val d.val :=
    (((fa.mono (by simp)).trans (fb.mono (by simp))).trans
      (fc.mono (by simp))).trans (fd.mono (by simp))
  have hd0 : d.val.tapes 0 = BitTape.blank := (hfd.tapes 0 (by simp)).trans h0
  have hd2 : d.val.tapes 2 = BitTape.blank := (hfd.tapes 2 (by simp)).trans h2
  have hd1 : d.val.tapes 1 = BitTape.shifted A 0 := (fd.tapes 1 (by simp)).trans hc1
  obtain ⟨addCost, e, hAdd, he, hep, he64, he0, he1, he2, heframe⟩ :=
    StoredAdd.simulation 64 (by decide) input tape A F 0 0 0 0 (PadWord.nonempty _) (PadWord.nonempty _)
      d.val d.property hd0 hd1 hd2 hd64
  have hval : addressValue A + addressValue F = i + f := by simp [A, F, addressValue_bits]
  simp only [hval, zero_add] at he64 he0 he2
  let e' := Store.ofState e
  have ee := Executes.call (StoredAdd.program 64) d e _ he (by
    have hh : (StoredAdd.program 64).code[96]? = some BitRAMInstruction.halt := by decide
    simpa only [hep] using hh)
  have fe : Frame {0, 1, 2, 64} d.val e'.val := by
    refine ⟨heframe.1, heframe.2.1, heframe.2.2.1, heframe.2.2.2.1, heframe.2.2.2.2.1, ?_⟩
    intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
    exact heframe.2.2.2.2.2.1 j (by omega) hj.2.2.2
  obtain ⟨incCost, g, hInc, eg, hg64, fg⟩ := increment_steps input tape P F.length e' he64
  have hg1 : g.val.tapes 1 = BitTape.shifted A 0 := (fg.tapes 1 (by simp)).trans he1
  obtain ⟨h, eh, hh1, fh⟩ := clear_steps {1} 1 (by simp) input tape A 0 g hg1
  have hh64 : h.val.tapes 64 = BitTape.shifted (widthBits i f) F.length :=
    (fh.tapes 64 (by simp)).trans hg64
  obtain ⟨t, et, ht64, ht1, ft⟩ := move_steps {1, 64} 64 1 (by simp) (by simp) (by decide)
    input tape (widthBits i f) F.length A.length h hh64 (by simpa using hh1)
  have ff : Frame {1, 64} e'.val t.val :=
    ((fg.mono (by simp)).trans (fh.mono (by simp))).trans ft
  have hall := ea.seq (eb.seq (ec.seq (ed.seq (ee.seq (eg.seq (eh.seq et))))))
  refine ⟨_, t, F.length, A.length, P.length, (F.length : ℤ) + (widthBits i f).length,
    ?_, hall, (ff.tapes 0 (by simp)).trans he0, ht1,
    (ff.tapes 2 (by simp)).trans he2, ht64,
    ((hfd.mono (by decide)).trans fe).trans (ff.mono (by decide))⟩
  have hA := PadWord.length_le i.bits
  have hF := PadWord.length_le f.bits
  have hP := IndexedAddress.sum_length_le i.bits f.bits
  simp only [addressValue_bits] at hP
  have hW := widthBits_length i f
  dsimp [A, F, P] at hAdd hInc ⊢
  omega

/-- After computing the width, multiply its actual stored binary word by a
preserved copy of the sample count. The canonical product is moved to tape60. -/
def productCode : Code :=
  .seq (.call (WordTransfer.clone 43 64))
    (.seq (.call (StoredProduct.program 64))
      (.seq (.call (WordTransfer.move 64 60)) (.call (TapeOps.clear 1))))

def code : Code := .seq widthCode productCode

def program : BitRAM := code.compile

theorem product_steps (input : List Bool) (tape : ℕ → Bool) (width : List Bool) (samples : ℕ)
    (ao wo zo yo so : ℤ) (hwidth : 0 < width.length) (s : Store)
    (h0 : s.val.tapes 0 = {BitTape.blank with head := ao})
    (h1 : s.val.tapes 1 = BitTape.shifted width wo)
    (h2 : s.val.tapes 2 = {BitTape.blank with head := zo})
    (h3 : s.val.tapes 3 = {BitTape.blank with head := yo})
    (h64 : s.val.tapes 64 = {BitTape.blank with head := so})
    (h60 : s.val.tapes 60 = BitTape.blank)
    (hsamples : s.val.tapes 43 = BitTape.ofList samples.bits) :
    ∃ cost t ro xo,
      cost ≤ 600 * (width.length + samples.bits.length + 2)^2 ∧
      Executes input tape productCode cost s t ∧
      t.val.tapes 0 = {BitTape.blank with head := ro} ∧
      t.val.tapes 1 = {BitTape.blank with head := wo + width.length} ∧
      t.val.tapes 2 = {BitTape.blank with head := xo} ∧
      t.val.tapes 3 = {BitTape.blank with head := yo + samples.bits.length} ∧
      t.val.tapes 64 = {BitTape.blank with head :=
        so + samples.bits.length + (addressValue width * samples).bits.length} ∧
      t.val.tapes 60 = BitTape.ofList (addressValue width * samples).bits ∧ Frame work s.val t.val := by
  obtain ⟨a, ea, ha64, fa⟩ := clone_steps {64} 43 64 (by simp) (by decide)
    input tape samples.bits 0 so s (by simpa [BitTape.shifted, BitTape.ofList] using hsamples) h64
  have ha0 := (fa.tapes 0 (by simp)).trans h0
  have ha1 := (fa.tapes 1 (by simp)).trans h1
  have ha2 := (fa.tapes 2 (by simp)).trans h2
  have ha3 := (fa.tapes 3 (by simp)).trans h3
  obtain ⟨mcost, b, ro, xo, hmcost, eb, hbp, hb64, hb0, hb1, hb2, hb3, hbframe⟩ :=
    StoredProduct.simulation 64 (by decide) input tape width samples.bits ao wo zo yo so hwidth
      a.val a.property ha0 ha1 ha2 ha3 ha64
  simp only [addressValue_bits] at hb64
  let b' := Store.ofState b
  have em := Executes.call (StoredProduct.program 64) a b _ eb (by
    have hh : (StoredProduct.program 64).code[120]? = some BitRAMInstruction.halt := by decide
    simpa only [hbp] using hh)
  have fb : Frame {0, 2, 3, 64} a.val b'.val := by
    refine ⟨hbframe.1, hbframe.2.1, hbframe.2.2.1, hbframe.2.2.2.1, hbframe.2.2.2.2.1, ?_⟩
    intro j hj
    by_cases hj1 : j = 1
    · subst j
      exact hb1.trans ha1.symm
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
      exact hbframe.2.2.2.2.2.1 j (by omega) hj.2.2.2
  have hb60 : b'.val.tapes 60 = BitTape.blank :=
    (fb.tapes 60 (by simp)).trans ((fa.tapes 60 (by simp)).trans h60)
  obtain ⟨c, ec, hc64, hc60, fc⟩ := move_steps {60, 64} 64 60 (by simp) (by simp) (by decide)
    input tape (addressValue width * samples).bits (so + samples.bits.length) 0 b' hb64 hb60
  have hc1 : c.val.tapes 1 = BitTape.shifted width wo := (fc.tapes 1 (by simp)).trans hb1
  obtain ⟨t, et, ht1, ft⟩ := clear_steps {1} 1 (by simp) input tape width wo c hc1
  have ff : Frame {1, 60, 64} b'.val t.val := (fc.mono (by decide)).trans (ft.mono (by decide))
  refine ⟨_, t, ro, xo, ?_, ea.seq (em.seq (ec.seq et)),
    (ff.tapes 0 (by simp)).trans hb0, ht1, (ff.tapes 2 (by simp)).trans hb2,
    (ff.tapes 3 (by simp)).trans hb3, (ft.tapes 64 (by simp)).trans hc64,
    ?_, ((fa.mono (by decide)).trans (fb.mono (by decide))).trans (ff.mono (by decide))⟩
  · have hprod := IndexedAddress.product_length_le width samples.bits
    simp only [addressValue_bits] at hprod
    nlinarith
  · simpa [BitTape.shifted, BitTape.ofList] using (ft.tapes 60 (by simp)).trans hc60

/-- The arithmetic preparation is polynomial in the three metadata word
lengths, rather than in the magnitude of the sample count. -/
def costBound (i f samples : ℕ) : ℕ := 1000 * (i.bits.length + f.bits.length + samples.bits.length + 6)^2

theorem steps (input : List Bool) (tape : ℕ → Bool) (i f samples : ℕ) (s : Store)
    (hblank : ∀ j ∈ work, s.val.tapes j = BitTape.blank)
    (hi : s.val.tapes 41 = BitTape.ofList i.bits)
    (hf : s.val.tapes 42 = BitTape.ofList f.bits)
    (hs : s.val.tapes 43 = BitTape.ofList samples.bits) :
    ∃ cost t ao wo zo yo so,
      cost ≤ costBound i f samples ∧ Executes input tape code cost s t ∧
      t.val.tapes 60 = BitTape.ofList (samples * (1 + i + f)).bits ∧
      t.val.tapes 0 = {BitTape.blank with head := ao} ∧
      t.val.tapes 1 = {BitTape.blank with head := wo} ∧
      t.val.tapes 2 = {BitTape.blank with head := zo} ∧
      t.val.tapes 3 = {BitTape.blank with head := yo} ∧
      t.val.tapes 64 = {BitTape.blank with head := so} ∧ Frame work s.val t.val := by
  obtain ⟨wc, w, ao, wo, zo, so, hwc, ew, hw0, hw1, hw2, hw64, fw⟩ :=
    width_steps input tape i f s (hblank 0 (by decide)) (hblank 1 (by decide))
      (hblank 2 (by decide)) (hblank 64 (by decide)) hi hf
  have hw3 : w.val.tapes 3 = BitTape.blank := (fw.tapes 3 (by simp)).trans (hblank 3 (by decide))
  have hw60 : w.val.tapes 60 = BitTape.blank := (fw.tapes 60 (by simp)).trans (hblank 60 (by decide))
  have hw43 : w.val.tapes 43 = BitTape.ofList samples.bits := (fw.tapes 43 (by simp)).trans hs
  obtain ⟨pc, t, ro, xo, hpc, ep, ht0, ht1, ht2, ht3, ht64, ht60, ft⟩ :=
    product_steps input tape (widthBits i f) samples ao wo zo 0 so (widthBits_nonempty i f) w
      hw0 hw1 hw2 hw3 hw64 hw60 hw43
  have htotal : addressValue (widthBits i f) * samples = samples * (1 + i + f) := by
    rw [widthBits_value, Nat.mul_comm]
  refine ⟨wc + pc, t, ro, wo + (widthBits i f).length, xo, samples.bits.length,
    so + samples.bits.length + (samples * (1 + i + f)).bits.length, ?_, ew.seq ep,
    by simpa only [htotal] using ht60, ht0, ht1, ht2, by simpa using ht3,
    by simpa only [htotal] using ht64, (fw.mono (by decide)).trans ft⟩
  have hwlen := widthBits_length i f
  have hpbound : (widthBits i f).length + samples.bits.length + 2 ≤
      i.bits.length + f.bits.length + samples.bits.length + 6 := by omega
  have hh := Nat.pow_le_pow_left hpbound 2
  dsimp [costBound]
  nlinarith

/-- Canonical loader-count bit width follows from actual multiplication. -/
theorem count_bits_length (i f samples : ℕ) :
    (samples * (1 + i + f)).bits.length ≤ samples.bits.length + i.bits.length + f.bits.length + 2 := by
  have h := IndexedAddress.product_length_le (widthBits i f) samples.bits
  rw [widthBits_value, addressValue_bits, Nat.mul_comm] at h
  have hw := widthBits_length i f
  omega

def loadCode : Code := .seq code LoadMessages.code

def loadProgram : BitRAM := loadCode.compile

def loadCostBound (i f samples : ℕ) : ℕ :=
  costBound i f samples + LoadMessages.costBound (samples * (1 + i + f))

/-- Composable preparation and loading, including the actual final address
word used to rewind the sequential input for the decoder's second pass. -/
theorem load_messages_steps {ι : Type*} {n : ℕ} (D : Target.WeightedDecoder ι n)
    (messages : D.Messages) (preceding suffix : List Bool) (randomTape : ℕ → Bool)
    (s : Store) (hhead : s.val.inputHead = preceding.length)
    (hblank : ∀ j ∈ work, s.val.tapes j = BitTape.blank)
    (haddress : s.val.tapes 61 = BitTape.blank)
    (hi : s.val.tapes 41 = BitTape.ofList D.format.integerBits.bits)
    (hf : s.val.tapes 42 = BitTape.ofList D.format.fractionalBits.bits)
    (hs : s.val.tapes 43 = BitTape.ofList D.sampleCount.bits) :
    ∃ cost t address,
      Executes (preceding ++ (Codec.messages D messages ++ suffix)) randomTape loadCode cost s t ∧
      cost ≤ loadCostBound D.format.integerBits D.format.fractionalBits D.sampleCount ∧
      t.val.inputHead = s.val.inputHead + (D.sampleCount * D.format.width : ℕ) ∧
      t.val.memory = MemoryWord.writeBits s.val.memory 0 (Codec.messages D messages) ∧
      t.val.tapes 61 = BitTape.shiftedEnd address 0 ∧
      addressValue address = D.sampleCount * D.format.width ∧
      address.length ≤ (D.sampleCount * D.format.width).bits.length ∧
      t.val.randomCursor = s.val.randomCursor ∧ t.val.output = s.val.output ∧
      (∀ j, j ∉ work → j ≠ 61 → t.val.tapes j = s.val.tapes j) ∧
      (∀ j ∈ ({0, 1, 2, 3, 64} : Finset ℕ), ∃ origin : ℤ,
        t.val.tapes j = {BitTape.blank with head := origin}) := by
  let input := preceding ++ (Codec.messages D messages ++ suffix)
  obtain ⟨pc, p, ao, wo, zo, yo, so, hpc, ep, hp60, hp0, hp1, hp2, hp3, hp64, fp⟩ :=
    steps input randomTape D.format.integerBits D.format.fractionalBits D.sampleCount s hblank hi hf hs
  have hphead : p.val.inputHead = preceding.length := fp.inputHead.trans hhead
  have hpaddress : p.val.tapes 61 = BitTape.blank := (fp.tapes 61 (by decide)).trans haddress
  have hpcount : p.val.tapes 60 = BitTape.ofList (Codec.messages D messages).length.bits := by
    simpa only [Codec.messages_length, Target.FixedPointFormat.width] using hp60
  obtain ⟨lc, t, address, el, hlc, hli, hla, hlav, hlal, hlm, fl⟩ :=
    LoadMessages.load_word preceding (Codec.messages D messages) suffix randomTape p hphead hpcount hpaddress
  refine ⟨pc + lc, t, address, ep.seq el, ?_, ?_, hlm.trans (by rw [fp.memory]), hla,
    by simpa only [Codec.messages_length] using hlav,
    by simpa only [Codec.messages_length] using hlal,
    fl.randomCursor.trans fp.randomCursor, fl.output.trans fp.output, ?_, ?_⟩
  · simpa only [loadCostBound, Codec.messages_length, Target.FixedPointFormat.width] using Nat.add_le_add hpc hlc
  · simpa only [Codec.messages_length, fp.inputHead] using hli
  · intro j hj hj61
    have hj60 : j ≠ 60 := by intro heq; subst j; exact hj (by decide)
    exact (fl.tapes j hj60 hj61).trans (fp.tapes j hj)
  · intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl
    · exact ⟨ao, (fl.tapes 0 (by decide) (by decide)).trans hp0⟩
    · exact ⟨wo, (fl.tapes 1 (by decide) (by decide)).trans hp1⟩
    · exact ⟨zo, (fl.tapes 2 (by decide) (by decide)).trans hp2⟩
    · exact ⟨yo, (fl.tapes 3 (by decide) (by decide)).trans hp3⟩
    · exact ⟨so, (fl.tapes 64 (by decide) (by decide)).trans hp64⟩

/-- Preparation and loading are one finite compiled program. The total bit
count is computed from persistent metadata, never supplied by a host step. -/
theorem load_messages {ι : Type*} {n : ℕ} (D : Target.WeightedDecoder ι n)
    (messages : D.Messages) (preceding suffix : List Bool) (randomTape : ℕ → Bool)
    (s : Store) (hhead : s.val.inputHead = preceding.length)
    (hblank : ∀ j ∈ work, s.val.tapes j = BitTape.blank)
    (haddress : s.val.tapes 61 = BitTape.blank)
    (hi : s.val.tapes 41 = BitTape.ofList D.format.integerBits.bits)
    (hf : s.val.tapes 42 = BitTape.ofList D.format.fractionalBits.bits)
    (hs : s.val.tapes 43 = BitTape.ofList D.sampleCount.bits) :
    ∃ t : BitRAMState,
      (runPriced (loadProgram.next (preceding ++ (Codec.messages D messages ++ suffix)) randomTape)
        (loadCostBound D.format.integerBits D.format.fractionalBits D.sampleCount + 1) s.val).finished = some t ∧
      (runPriced (loadProgram.next (preceding ++ (Codec.messages D messages ++ suffix)) randomTape)
        (loadCostBound D.format.integerBits D.format.fractionalBits D.sampleCount + 1) s.val).instructions ≤
          loadCostBound D.format.integerBits D.format.fractionalBits D.sampleCount ∧
      t.inputHead = s.val.inputHead + (D.sampleCount * D.format.width : ℕ) ∧
      (∀ i (hi : i < (Codec.messages D messages).length), t.memory i = (Codec.messages D messages)[i]) ∧
      (∀ i, D.sampleCount * D.format.width ≤ i → t.memory i = s.val.memory i) ∧
      t.randomCursor = s.val.randomCursor ∧ t.output = s.val.output ∧
      (∀ j, j ∉ work → j ≠ 61 → t.tapes j = s.val.tapes j) ∧
      (∀ j ∈ ({0, 1, 2, 3, 64} : Finset ℕ), ∃ origin : ℤ,
        t.tapes j = {BitTape.blank with head := origin}) := by
  obtain ⟨cost, t, address, he, hc, htinput, htmemory, _, _, _, htr, hto, htf, hts⟩ :=
    load_messages_steps D messages preceding suffix randomTape s hhead hblank haddress hi hf hs
  obtain ⟨hfinish, hinstructions⟩ := he.compiled_run
    (loadCostBound D.format.integerBits D.format.fractionalBits D.sampleCount + 1) (by omega)
  refine ⟨t.place loadCode.size, hfinish, hinstructions.trans_le hc, htinput, ?_, ?_, htr, hto, htf, hts⟩
  · intro i hil
    change t.val.memory i = _
    rw [htmemory]
    simpa using MemoryWord.writeBits_inside s.val.memory 0 (Codec.messages D messages) i hil
  · intro i hil
    change t.val.memory i = _
    rw [htmemory]
    exact MemoryWord.writeBits_outside s.val.memory 0 (Codec.messages D messages) i
      (Or.inr (by simpa only [zero_add, Codec.messages_length] using hil))

end Maxwell.Cost.DecoderParser.MetadataProduct
