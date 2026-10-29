import Maxwell.Cost.NormalizeCoefficient.PadReverse.Tapes

namespace Maxwell.Cost.NormalizeCoefficient.PadReverse

theorem padded_succ (width : ℕ) (bits : List Bool) (h : bits.length ≤ width + 1) :
    padded (width + 1) bits = bits.headD false :: padded width bits.tail := by
  cases bits with
  | nil => simp [padded, List.replicate_succ]
  | cons b bs =>
    have he : width + 1 - (bs.length + 1) = width - bs.length := by omega
    simp [padded, he]

theorem next_source (s : BitRAMState) (bits : List Bool) (origin : ℤ)
    (h : s.tapes 4 = BitTape.shifted bits origin) :
    (nextState s).tapes 4 = BitTape.shifted bits.tail (origin + 1) := by
  simp only [nextState, Function.update_of_ne (show (4 : ℕ) ≠ 82 by omega),
    Function.update_self, h]
  cases bits with
  | nil => exact erase_move_nil origin
  | cons b bs => exact BitTape.shifted_erase_move b bs origin

theorem next_target (s : BitRAMState) (bits preceding : List Bool) (sourceOrigin targetOrigin : ℤ)
    (hsource : s.tapes 4 = BitTape.shifted bits sourceOrigin)
    (htarget : s.tapes 83 = BitTape.shifted preceding targetOrigin) :
    (nextState s).tapes 83 = BitTape.shifted (bits.headD false :: preceding) (targetOrigin - 1) := by
  simp only [nextState, Function.update_of_ne (show (83 : ℕ) ≠ 82 by omega),
    Function.update_of_ne (show (83 : ℕ) ≠ 4 by omega), Function.update_self, hsource, htarget,
    BitTape.shifted_read]
  have he : bits.head?.getD false = bits.headD false := by cases bits <;> rfl
  simpa only [he, BitTape.shifted] using prepend_word preceding targetOrigin (bits.headD false)

/-- The loop uses only actual tape reads. Its width is witnessed by the
zero prefix and terminal one on the persistent power-of-two tape. -/
theorem loop (input : List Bool) (tape : ℕ → Bool) (width : ℕ)
    (bits preceding : List Bool) (hwidth : bits.length ≤ width)
    (sourceOrigin targetOrigin powerOrigin : ℤ) (cells : ℤ → Option Bool)
    (s : BitRAMState) (hpc : s.pc = 0)
    (hsource : s.tapes 4 = BitTape.shifted bits sourceOrigin)
    (htarget : s.tapes 83 = BitTape.shifted preceding targetOrigin)
    (hpower : s.tapes 82 = ⟨powerOrigin, cells⟩)
    (hfalse : ∀ k : ℕ, k < width → cells (powerOrigin + k) = some false)
    (htrue : cells (powerOrigin + width) = some true) :
    ∃ t, PricedSteps (program.next input tape) (11*width+3) s t ∧ t.pc = 9 ∧
      t.tapes 4 = {BitTape.blank with head := sourceOrigin + width} ∧
      t.tapes 83 = BitTape.shifted ((padded width bits).reverse ++ preceding) (targetOrigin - width) ∧
      t.tapes 82 = ⟨powerOrigin + width, cells⟩ ∧ LoopFrame s t := by
  induction width generalizing bits preceding sourceOrigin targetOrigin powerOrigin s with
  | zero =>
    have hb : bits = [] := List.length_eq_zero_iff.mp (by omega)
    subst bits
    have hread : (s.tapes 82).read = some true := by simpa [hpower, BitTape.read] using htrue
    refine ⟨exitState s, finish input tape s hpc hread, rfl, ?_, ?_, ?_, exit_frame s⟩
    · simpa [exitState] using hsource
    · simpa [exitState, padded] using htarget
    · simpa [exitState] using hpower
  | succ width ih =>
    have hread : (s.tapes 82).read = some false := by
      simpa [hpower, BitTape.read] using hfalse 0 (by omega)
    have hh := cycle input tape s hpc hread
    have htail : bits.tail.length ≤ width := by simpa using (by omega : bits.length - 1 ≤ width)
    have hnp : (nextState s).tapes 82 = ⟨powerOrigin + 1, cells⟩ := by
      simp [nextState, hpower]
    have hnf : ∀ k : ℕ, k < width → cells (powerOrigin + 1 + k) = some false := by
      intro k hk
      convert hfalse (k+1) (by omega) using 1; push_cast; ring_nf
    have hnt : cells (powerOrigin + 1 + width) = some true := by
      convert htrue using 1; push_cast; ring_nf
    obtain ⟨t, ht, htp, hts, htt, htpow, htf⟩ := ih bits.tail
      (bits.headD false :: preceding) htail (sourceOrigin+1) (targetOrigin-1)
      (powerOrigin+1) (nextState s) rfl (next_source s bits sourceOrigin hsource)
      (next_target s bits preceding sourceOrigin targetOrigin hsource htarget) hnp hnf hnt
    refine ⟨t, ?_, htp, ?_, ?_, ?_, (next_frame s).trans htf⟩
    · convert hh.trans ht using 1; omega
    · convert hts using 1; push_cast; ring_nf
    · rw [padded_succ width bits hwidth, List.reverse_cons, List.append_assoc]
      convert htt using 1; simp only [List.singleton_append]; push_cast; ring_nf
    · convert htpow using 1; push_cast; ring_nf

end Maxwell.Cost.NormalizeCoefficient.PadReverse
