import Maxwell.Cost.RationalAccumulator.Initialize
import Maxwell.Cost.Structured.Primitive

namespace Maxwell.Cost.NormalizeCoefficient

open Structured RationalAccumulator

def values (q : Codec.RationalPair) (scaleNum scaleDen precision : ℕ) : ℕ → ℕ :=
  Function.update (Function.update (Function.update (Function.update
    (Function.update (fun _ => 0) 30 q.numerator.natAbs) 31 q.denominator)
      32 scaleNum) 33 scaleDen) 34 (2^precision)

/-- Cloning a persistent operand restores that operand's original head. -/
theorem clone_external (source target : ℕ) (hs : 37 ≤ source)
    (ht : 30 ≤ target) (ht' : target ≤ 36)
    (input : List Bool) (tape : ℕ → Bool) (v : ℕ → ℕ) (n : ℕ) (s : Store)
    (hbank : Bank s.val v) (hready : Scratch s.val 0) (hzero : v target = 0)
    (hword : Word s.val source n) :
    ∃ t : Store, Executes input tape (.call (WordTransfer.clone source target))
      (15*n.bits.length+17) s t ∧
      Bank t.val (Function.update v target n) ∧ Scratch t.val 0 ∧
      RationalAccumulator.Frame s.val t.val := by
  obtain ⟨so, hsource⟩ := hword
  have hh := hbank target ht ht'
  rw [hzero, zero_word_iff_blank] at hh
  obtain ⟨xo, htarget⟩ := hh
  obtain ⟨t, he, hp, hts, htt, hf⟩ := WordTransfer.clone_steps source target (by omega)
    input tape n.bits so xo s.val s.property hsource htarget
  refine ⟨Store.ofState t, ?_, ?_, ?_, ?_⟩
  · exact Executes.call _ _ _ _ he (by
      simp [WordTransfer.clone, hp, Copy.program, Rewind.program, BitRAMInstruction.relocate])
  · intro i hi hi'
    by_cases hit : i = target
    · subst i
      exact ⟨xo, by simpa only [Function.update_self, Store.ofState] using htt⟩
    · simp only [Function.update_of_ne hit]
      exact word_of_eq (hf.2.2.2.2.2.1 i (by omega) hit) (hbank i hi hi')
  · exact ⟨blank_of_eq (hf.2.2.2.2.2.1 0 (by omega) (by omega)) hready.1,
      word_of_eq (hf.2.2.2.2.2.1 1 (by omega) (by omega)) hready.2.1,
      blank_of_eq (hf.2.2.2.2.2.1 2 (by omega) (by omega)) hready.2.2.1,
      blank_of_eq (hf.2.2.2.2.2.1 3 (by omega) (by omega)) hready.2.2.2⟩
  · rcases hf with ⟨ha, hi, hm, hr, ho, htapes, hg⟩
    refine ⟨ha, hi, hm, hr, ho, ?_, fun i _ h24 h25 h26 h27 => hg i h24 h25 h26 h27⟩
    intro i _ hib
    by_cases his : i = source
    · subst i; exact hts.trans hsource.symm
    · exact htapes i his (by omega)

def loadCode : Code := .seq (TakeParsed.code 12 30) (.seq (TakeParsed.code 13 31)
  (.seq (.call (WordTransfer.clone 80 32))
    (.seq (.call (WordTransfer.clone 81 33)) (.call (WordTransfer.clone 82 34)))))

theorem load (input : List Bool) (tape : ℕ → Bool) (q : Codec.RationalPair)
    (scaleNum scaleDen precision : ℕ) (s : Store)
    (hbank : Bank s.val (fun _ => 0)) (hready : Scratch s.val 0)
    (hnum : s.val.tapes 12 = BitTape.atEnd q.numerator.natAbs.bits)
    (hden : s.val.tapes 13 = BitTape.atEnd q.denominator.bits)
    (hscaleNum : Word s.val 80 scaleNum) (hscaleDen : Word s.val 81 scaleDen)
    (hpower : Word s.val 82 (2^precision)) :
    ∃ t : Store, Executes input tape loadCode
      (21*(q.numerator.natAbs.bits.length+q.denominator.bits.length) +
        15*(scaleNum.bits.length+scaleDen.bits.length+(2^precision).bits.length)+95) s t ∧
      Bank t.val (values q scaleNum scaleDen precision) ∧ Scratch t.val 0 ∧
      t.val.tapes 12 = BitTape.blank ∧ t.val.tapes 13 = BitTape.blank ∧ ParseFrame s.val t.val := by
  let v1 := Function.update (fun _ : ℕ => 0) 30 q.numerator.natAbs
  let v2 := Function.update v1 31 q.denominator
  let v3 := Function.update v2 32 scaleNum
  let v4 := Function.update v3 33 scaleDen
  obtain ⟨a, ha, hab, har, ha12, haf, haf'⟩ := take_bank 12 30 (Or.inl rfl)
    (by omega) (by omega) input tape (fun _ => 0) q.numerator.natAbs s hbank hready rfl hnum
  obtain ⟨b, hb, hbb, hbr, hb13, hbf, hbf'⟩ := take_bank 13 31 (Or.inr rfl)
    (by omega) (by omega) input tape v1 q.denominator a hab har (by simp [v1])
    ((haf.2.2.2.2.2.1 13 (by omega) (by omega)).trans hden)
  have hsab := haf'.trans hbf'
  have hbNum := word_of_eq (hsab.2.2.2.2.2.1 80 (by omega) (by omega) (by omega)
    (Or.inr (by omega))) hscaleNum
  obtain ⟨c, hc, hcb, hcr, hcf⟩ := clone_external 80 32 (by omega) (by omega) (by omega)
    input tape v2 scaleNum b hbb hbr (by simp [v2, v1]) hbNum
  have hsac := hsab.trans (parseFrame_of_frame hcf)
  have hcDen := word_of_eq (hsac.2.2.2.2.2.1 81 (by omega) (by omega) (by omega)
    (Or.inr (by omega))) hscaleDen
  obtain ⟨d, hd, hdb, hdr, hdf⟩ := clone_external 81 33 (by omega) (by omega) (by omega)
    input tape v3 scaleDen c hcb hcr (by simp [v3, v2, v1]) hcDen
  have hsad := hsac.trans (parseFrame_of_frame hdf)
  have hdPow := word_of_eq (hsad.2.2.2.2.2.1 82 (by omega) (by omega) (by omega)
    (Or.inr (by omega))) hpower
  obtain ⟨t, ht, htb, htr, htf⟩ := clone_external 82 34 (by omega) (by omega) (by omega)
    input tape v4 (2^precision) d hdb hdr (by simp [v4, v3, v2, v1]) hdPow
  have htail := (hcf.trans hdf).trans htf
  refine ⟨t, ?_, htb, htr, ?_, ?_, hsad.trans (parseFrame_of_frame htf)⟩
  · have he := ha.seq (hb.seq (hc.seq (hd.seq ht)))
    convert he using 1 <;> first | rfl | omega
  · exact (htail.2.2.2.2.2.1 12 (by omega) (Or.inl (by omega))).trans
      ((hbf.2.2.2.2.2.1 12 (by omega) (by omega)).trans ha12)
  · exact (htail.2.2.2.2.2.1 13 (by omega) (Or.inl (by omega))).trans hb13

end Maxwell.Cost.NormalizeCoefficient
