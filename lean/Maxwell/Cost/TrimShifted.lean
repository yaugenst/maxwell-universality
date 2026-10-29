import Maxwell.Cost.CanonicalBits

namespace Maxwell.Cost

def BitTape.shiftedBeforeEnd (bits : List Bool) (origin : ℤ) : BitTape :=
  {BitTape.shifted bits origin with head := origin + bits.length - 1}

theorem BitTape.shiftedBeforeEnd_read (bits : List Bool) (b : Bool) (origin : ℤ) :
    (BitTape.shiftedBeforeEnd (bits ++ [b]) origin).read = some b := by
  have hhead : origin + ((bits ++ [b]).length : ℤ) - 1 = origin + bits.length := by
    simp
    omega
  dsimp only [BitTape.shiftedBeforeEnd, BitTape.shifted, BitTape.read]
  rw [hhead]
  simp

theorem BitTape.shiftedBeforeEnd_nil_read (origin : ℤ) :
    (BitTape.shiftedBeforeEnd [] origin).read = none := by
  simp [BitTape.shiftedBeforeEnd, BitTape.shifted, BitTape.read]

theorem BitTape.shifted_erase_last (bits : List Bool) (b : Bool) (origin : ℤ) :
    {(BitTape.shiftedBeforeEnd (bits ++ [b]) origin).write none with
      head := (BitTape.shiftedBeforeEnd (bits ++ [b]) origin).head - 1} =
      BitTape.shiftedBeforeEnd bits origin := by
  apply BitTape.ext
  · simp [BitTape.shiftedBeforeEnd]
    omega
  · funext p
    have hhead : origin + ((bits ++ [b]).length : ℤ) - 1 = origin + bits.length := by
      simp
      omega
    simp only [BitTape.write, BitTape.shiftedBeforeEnd, BitTape.shifted, hhead]
    by_cases heq : p = origin + (bits.length : ℤ)
    · subst p
      simp
    · rw [Function.update_of_ne heq]
      by_cases hp : origin ≤ p
      · simp only [ite_eq_left hp]
        have hn : (p - origin).toNat ≠ bits.length := by omega
        by_cases hlt : (p - origin).toNat < bits.length
        · simp [List.getElem?_append, hlt]
        · have hgt : bits.length < (p - origin).toNat := by omega
          simp [List.getElem?_append, hlt,
            show (p - origin).toNat - bits.length ≠ 0 by omega]
      · simp [hp]

namespace TapeOps

theorem trim_shifted_loop (source : ℕ) (origin : ℤ) (input : List Bool)
    (randomTape : ℕ → Bool) (core : List Bool) (hcore : CanonicalBits core) (n : ℕ)
    (s : BitRAMState) (hpc : s.pc = 1)
    (htape : s.tapes source = BitTape.shiftedBeforeEnd (core ++ List.replicate n false) origin) :
    ∃ cost t, cost ≤ 7 * n + 5 ∧
      PricedSteps ((trim source).next input randomTape) cost s t ∧
      t.pc = 8 ∧ t.tapes source = BitTape.shiftedEnd core origin := by
  induction n generalizing s with
  | zero =>
    simp only [List.replicate_zero, List.append_nil] at htape
    rcases hcore with rfl | ⟨preceding, rfl⟩
    · have hread : (s.tapes source).read = none := by
        rw [htape]
        exact BitTape.shiftedBeforeEnd_nil_read origin
      refine ⟨4, trimExit source s false, by omega,
        trim_blank_block source input randomTape s hpc hread, rfl, ?_⟩
      simp [trimExit, htape, BitTape.shiftedBeforeEnd, BitTape.shiftedEnd]
    · have hread : (s.tapes source).read = some true := by
        rw [htape]
        exact BitTape.shiftedBeforeEnd_read preceding true origin
      refine ⟨5, trimExit source s true, by omega,
        trim_true_block source input randomTape s hpc hread, rfl, ?_⟩
      simp [trimExit, htape, BitTape.shiftedBeforeEnd, BitTape.shiftedEnd]
  | succ n ih =>
    have hword : core ++ List.replicate (n + 1) false =
        (core ++ List.replicate n false) ++ [false] := by
      rw [List.replicate_succ']
      simp [List.append_assoc]
    have hread : (s.tapes source).read = some false := by
      rw [htape, hword]
      exact BitTape.shiftedBeforeEnd_read _ false origin
    have hstep := trim_zero_block source input randomTape s hpc hread
    have hnext : (trimNext source s).tapes source =
        BitTape.shiftedBeforeEnd (core ++ List.replicate n false) origin := by
      simp only [trimNext, Function.update_self, htape, hword]
      exact BitTape.shifted_erase_last _ false origin
    obtain ⟨cost, t, hc, hs, hp, ht⟩ := ih (trimNext source s) rfl hnext
    exact ⟨7 + cost, t, by omega, hstep.trans hs, hp, ht⟩

/-- The existing fixed trim code works at every integer origin, including
negative positions introduced by multiplication's left-shift operation. -/
theorem trim_shifted_steps (source : ℕ) (origin : ℤ) (input : List Bool)
    (randomTape : ℕ → Bool) (bits : List Bool) (s : BitRAMState) (hpc : s.pc = 0)
    (htape : s.tapes source = BitTape.shiftedEnd bits origin) :
    ∃ cost t core, cost ≤ 7 * bits.length + 6 ∧
      PricedSteps ((trim source).next input randomTape) cost s t ∧
      t.pc = 8 ∧ t.tapes source = BitTape.shiftedEnd core origin ∧
      CanonicalBits core ∧ addressValue core = addressValue bits ∧
      core.length ≤ bits.length ∧ Frame source source s t := by
  obtain ⟨core, n, hbits, hcore⟩ := trailing_zero_decomposition bits
  have hstart := trim_start_block source input randomTape s hpc
  have ht : (trimStart source s).tapes source =
      BitTape.shiftedBeforeEnd (core ++ List.replicate n false) origin := by
    simp [trimStart, htape, hbits, BitTape.shiftedEnd, BitTape.shiftedBeforeEnd]
  obtain ⟨cost, t, hc, hsteps, hp, hout⟩ :=
    trim_shifted_loop source origin input randomTape core hcore n (trimStart source s) rfl ht
  have hlen : bits.length = core.length + n := by simp [hbits]
  have hall := hstart.trans hsteps
  refine ⟨1 + cost, t, core, by omega, hall, hp, hout, hcore, ?_, by omega,
    trim_steps_frame source input randomTape hall⟩
  rw [hbits, addressValue_append_zeros]

theorem trim_shifted_canonical_steps (source : ℕ) (origin : ℤ) (input : List Bool)
    (randomTape : ℕ → Bool) (bits : List Bool) (s : BitRAMState) (hpc : s.pc = 0)
    (htape : s.tapes source = BitTape.shiftedEnd bits origin) :
    ∃ cost t, cost ≤ 7 * bits.length + 6 ∧
      PricedSteps ((trim source).next input randomTape) cost s t ∧
      t.pc = 8 ∧ t.tapes source = BitTape.shiftedEnd (addressValue bits).bits origin ∧
      (addressValue bits).bits.length ≤ bits.length ∧ Frame source source s t := by
  obtain ⟨cost, t, core, hc, hs, hp, ht, hcore, hvalue, hlen, hf⟩ :=
    trim_shifted_steps source origin input randomTape bits s hpc htape
  have hcanonical : (addressValue bits).bits = core := by
    rw [← hvalue]
    exact canonicalBits_bits hcore
  exact ⟨cost, t, hc, hs, hp, hcanonical ▸ ht, by simpa [hcanonical] using hlen, hf⟩

theorem trim_shifted_run (source : ℕ) (origin : ℤ) (input : List Bool)
    (randomTape : ℕ → Bool) (bits : List Bool) (s : BitRAMState) (hpc : s.pc = 0)
    (htape : s.tapes source = BitTape.shiftedEnd bits origin) :
    ∃ t, (runPriced ((trim source).next input randomTape)
        (7 * bits.length + 7) s).finished = some t ∧
      (runPriced ((trim source).next input randomTape)
        (7 * bits.length + 7) s).instructions ≤ 7 * bits.length + 6 ∧
      t.tapes source = BitTape.shiftedEnd (addressValue bits).bits origin ∧
      (addressValue bits).bits.length ≤ bits.length ∧ Frame source source s t := by
  obtain ⟨cost, t, hc, hs, hp, ht, hlen, hf⟩ :=
    trim_shifted_canonical_steps source origin input randomTape bits s hpc htape
  have hhalt : (trim source).next input randomTape t = none := by
    simp [BitRAM.next, trim, hp]
  have hr := hs.runPriced_ge hhalt (7 * bits.length + 7) (by omega)
  exact ⟨t, hr.1, hr.2 ▸ hc, ht, hlen, hf⟩

end TapeOps
end Maxwell.Cost
