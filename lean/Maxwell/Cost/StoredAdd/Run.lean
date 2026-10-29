import Maxwell.Cost.StoredAdd

namespace Maxwell.Cost.StoredAdd

theorem run (storage : ℕ) (hstorage : 3 ≤ storage)
    (input : List Bool) (tape : ℕ → Bool) (xs ys : List Bool)
    (ao xo zo storageOrigin : ℤ) (hxs : 0 < xs.length) (hys : 0 < ys.length)
    (s : BitRAMState) (hpc : s.pc = 0)
    (h0 : s.tapes 0 = {BitTape.blank with head := ao})
    (h1 : s.tapes 1 = BitTape.shifted xs xo)
    (h2 : s.tapes 2 = {BitTape.blank with head := zo})
    (hword : s.tapes storage = BitTape.shifted ys storageOrigin) :
    ∃ t,
      (runPriced ((program storage).next input tape)
        (100 * (xs.length + ys.length + 2) + 1) s).finished = some t ∧
      (runPriced ((program storage).next input tape)
        (100 * (xs.length + ys.length + 2) + 1) s).instructions ≤
          100 * (xs.length + ys.length + 2) ∧
      t.tapes storage = BitTape.shifted (addressValue xs + addressValue ys).bits
        (storageOrigin + ys.length) ∧
      t.tapes 0 = {BitTape.blank with head := ao + ys.length} ∧
      t.tapes 1 = BitTape.shifted xs xo ∧
      t.tapes 2 = {BitTape.blank with head := zo + (addressValue xs + addressValue ys).bits.length} ∧
      Frame storage s t := by
  obtain ⟨cost, t, hc, hs, hp, hw, hzero, hone, htwo, hf⟩ :=
    simulation storage hstorage input tape xs ys ao xo zo storageOrigin hxs hys
      s hpc h0 h1 h2 hword
  have halt : (program storage).next input tape t = none := by
    simp [BitRAM.next, program, hp, WordTransfer.move, TapeOps.copyClear, rippleAdder,
      RewindOvershoot.program, RewindOvershoot.preamble, BitRAM.link, Rewind.program,
      TapeOps.clear, NormalizeWord.program, ScanForward.program, TapeOps.trim,
      BitRAMInstruction.relocate]
  have hr := hs.runPriced_ge halt (100 * (xs.length + ys.length + 2) + 1) (by omega)
  exact ⟨t, hr.1, hr.2 ▸ hc, hw, hzero, hone, htwo, hf⟩

end Maxwell.Cost.StoredAdd
