import Maxwell.Cost.SignedRound.Decision

namespace Maxwell.Cost.SignedRound.Remainder

open Structured RationalAccumulator

def doubleCode : Code := .seq (Code.atom (.literal 26 false))
  (.seq (Code.atom (.tapeLeft 0)) (Code.atom (.writeTape 0 26)))

def doubled (s : Store) : Store := Store.ofState {s.val with
  registers := Function.update s.val.registers 26 false
  tapes := Function.update s.val.tapes 0
    (({s.val.tapes 0 with head := (s.val.tapes 0).head - 1}).write (some false))}

theorem double_executes (input : List Bool) (tape : ℕ → Bool) (s : Store) :
    Executes input tape doubleCode 6 s (doubled s) := by
  have ha := Executes.literal input tape s 26 false
  let a := Store.ofState (s.val.setRegister 26 false)
  have hb := Executes.tapeLeft input tape a 0
  let b := Store.ofState (a.val.setTape 0 {a.val.tapes 0 with head := (a.val.tapes 0).head - 1})
  have hc := Executes.writeTape input tape b 0 26
  convert ha.seq (hb.seq hc) using 1 <;>
    simp [doubleCode, doubled, a, b, Store.ofState, BitRAMState.setRegister, BitRAMState.setTape]

theorem doubled_word (s : Store) (bits : List Bool) (origin : ℤ)
    (h : s.val.tapes 0 = BitTape.shifted bits origin) :
    (doubled s).val.tapes 0 = BitTape.shifted (false :: bits) (origin - 1) := by
  simpa [doubled, Store.ofState, h, BitTape.shifted] using Division.prepend_bit bits origin false

theorem doubled_frame (s : Store) : Frame 3 s.val (doubled s).val := by
  simp [Frame, doubled, Store.ofState]
  constructor
  · intro i hi; simp [show i ≠ 0 by omega]
  · intro i _ hi _; simp [show i ≠ 26 by omega]

def code : Code := .seq doubleCode
  (.seq (.call SignedDifference.program)
    (.seq (.call (Rewind.program 2))
      (.seq (.call Decision.program)
        (.seq (eraseOvershootCode 0)
          (.seq (.call (RewindOvershoot.program 1)) (.call (TapeOps.clear 2)))))))

private theorem canonical_length_le (bs : List Bool) : (addressValue bs).bits.length ≤ bs.length := by
  obtain ⟨core, n, hbs, hc⟩ := TapeOps.trailing_zero_decomposition bs
  rw [hbs, TapeOps.addressValue_append_zeros, TapeOps.canonicalBits_bits hc]
  simp

/-- The finite remainder test treats negative ties strictly and positive
ties inclusively. It clears its scratch and restores the divisor word. -/
theorem executes (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (bits : List Bool) (denominator : ℕ) (hd : 0 < denominator)
    (ro xo zo : ℤ) (negative : Bool)
    (h0 : s.val.tapes 0 = BitTape.shifted bits ro)
    (h1 : s.val.tapes 1 = BitTape.shifted denominator.bits xo)
    (h2 : s.val.tapes 2 = {BitTape.blank with head := zo})
    (hsg : s.val.registers 35 = negative) :
    ∃ cost, ∃ t : Store, cost ≤ 300 * (bits.length + denominator.bits.length + 4) ∧
      Executes input tape code cost s t ∧
      t.val.registers 36 = (if negative then decide (denominator < 2 * addressValue bits)
        else decide (denominator ≤ 2 * addressValue bits)) ∧
      Blank t.val 0 ∧ t.val.tapes 1 = BitTape.shifted denominator.bits xo ∧
      Blank t.val 2 ∧ Frame 3 s.val t.val := by
  let a := doubled s
  have hea := double_executes input tape s
  have haf := doubled_frame s
  have ha1 : a.val.tapes 1 = BitTape.shifted denominator.bits xo := by
    simpa [a, doubled, Store.ofState] using h1
  have ha2 : a.val.tapes 2 = {BitTape.blank with head := zo} := by
    simpa [a, doubled, Store.ofState] using h2
  obtain ⟨diffCost, diff, no, hdCost, hed, hdp, hdSign, hd2, hd0, hd1⟩ :=
    SignedDifference.simulation_cleanup input tape a.val (false :: bits) denominator.bits
      (ro - 1) xo zo a.property (doubled_word s bits ro h0) ha1 ha2
  have hdf := SignedDifference.execution_frame input tape hed
  let d : Store := Store.ofState diff
  have hed' : Executes input tape (.call SignedDifference.program) (diffCost + 1) a d :=
    Executes.call _ _ _ _ hed (by
      simp [SignedDifference.program, hdp, SignedDifference.padProgram, Subtraction.program,
        Subtraction.swappedProgram, BitRAM.renameTapes, RewindOvershoot.program,
        RewindOvershoot.preamble, Rewind.program, BitRAM.link, TapeOps.clear, TapeOps.trim,
        BitRAMInstruction.relocate])
  let mag := addressValue (SignedDifference.magnitude (false :: bits) denominator.bits)
  have hr := WordTransfer.rewind_shifted 2 no input tape mag.bits d.val d.property hd2
  let r : Store := Store.ofState (Rewind.finishAt 2 no d.val)
  have her : Executes input tape (.call (Rewind.program 2)) (4 * mag.bits.length + 6) d r :=
    Executes.call _ _ _ _ hr.1 (by simp [Rewind.program, Rewind.finishAt])
  have hrs : r.val.registers 23 = SignedDifference.sign (false :: bits) denominator.bits := by
    simpa [r, d, Store.ofState, Rewind.finishAt] using hdSign
  have hrsg : r.val.registers 35 = negative :=
    (frame_rewind 3 2 (by omega) no d.val).sign.trans
      ((frame_of_difference hdf).sign.trans (haf.sign.trans hsg))
  obtain ⟨decCost, e, heCost, hee, heflag, hef⟩ := Decision.executes input tape r mag no negative
    (SignedDifference.sign (false :: bits) denominator.bits) hr.2 hrsg hrs
  let ps := SignedDifference.padded (false :: bits)
  let qs := SignedDifference.padded denominator.bits
  let distance := max ps.length qs.length
  have he0 : e.val.tapes 0 = {BitTape.shifted ps (ro - 1) with head := ro - 1 + distance} := by
    have hh : r.val.tapes 0 = {BitTape.shifted ps (ro - 1) with head := ro - 1 + distance} := by
      simpa [r, d, Store.ofState, Rewind.finishAt, distance, ps, qs] using hd0
    exact (hef.2.2.2.2.2.1 0 (by omega)).trans hh
  obtain ⟨f, hef', hf0, hff⟩ := erase_overshoot 0 input tape ps (ro - 1) distance
    (SignedDifference.padded_pos _) (le_max_left _ _) e he0
  have hdenPadded : qs = denominator.bits := by
    have hne : denominator.bits ≠ [] := by
      intro hh
      have hl := bits_nonempty hd
      simp [hh] at hl
    simp [qs, SignedDifference.padded, hne]
  have he1 : e.val.tapes 1 = {BitTape.shifted qs xo with head := xo + distance} := by
    have hh : r.val.tapes 1 = {BitTape.shifted qs xo with head := xo + distance} := by
      simpa [r, d, Store.ofState, Rewind.finishAt, distance, ps, qs] using hd1
    exact (hef.2.2.2.2.2.1 1 (by omega)).trans hh
  have hf1 := (hff.2.2.2.2.2.1 1 (by omega) (by omega)).trans he1
  have hrew := WordTransfer.rewind_overshoot_shifted 1 xo input tape qs distance
    (SignedDifference.padded_pos _) (le_max_right _ _) f.val f.property hf1
  let g : Store := Store.ofState (RewindOvershoot.finish 1 xo f.val)
  have heg : Executes input tape (.call (RewindOvershoot.program 1)) (4 * distance + 7) f g :=
    Executes.call _ _ _ _ hrew.1 (by
      simp [RewindOvershoot.program, RewindOvershoot.preamble, RewindOvershoot.finish,
        BitRAM.link, Rewind.program, Rewind.finishAt])
  have hg2 : g.val.tapes 2 = BitTape.shifted mag.bits no := by
    have he2 : e.val.tapes 2 = BitTape.shifted mag.bits no :=
      (hef.2.2.2.2.2.1 2 (by omega)).trans hr.2
    have hh := (hff.2.2.2.2.2.1 2 (by omega) (by omega)).trans he2
    simpa [g, Store.ofState, RewindOvershoot.finish, Rewind.finishAt] using hh
  obtain ⟨cleared, ht, htp, ht2, htf⟩ := TapeOps.clear_steps 2 input tape mag.bits no
    g.val g.property hg2
  let t : Store := Store.ofState cleared
  have het : Executes input tape (.call (TapeOps.clear 2)) (6 * mag.bits.length + 4) g t :=
    Executes.call _ _ _ _ ht (by simp [TapeOps.clear, htp])
  have hgf : Frame 3 f.val g.val := frame_rewind 3 1 (by omega) xo f.val
  have htf' := WordTransfer.frame_of_copy htf
  have hlast : Frame 3 e.val t.val :=
    ((frame_of_transfer (by omega) (by omega) hff).trans hgf).trans
      (frame_of_transfer (by omega) (by omega) htf')
  refine ⟨6 + ((diffCost + 1) + ((4 * mag.bits.length + 6) +
      (decCost + ((4 * distance + 6 * ps.length + 11) +
        ((4 * distance + 7) + (6 * mag.bits.length + 4)))))), t, ?_,
    hea.seq (hed'.seq (her.seq (hee.seq (hef'.seq (heg.seq het))))), ?_, ?_, ?_,
    ⟨no + mag.bits.length, ht2⟩,
    (((haf.trans (frame_of_difference hdf)).trans (frame_rewind 3 2 (by omega) no d.val)).trans
      (hef.mono (by omega))).trans hlast⟩
  · have hpLength := SignedDifference.padded_length (false :: bits)
    have hqLength := SignedDifference.padded_length denominator.bits
    have hnLength := canonical_length_le (SignedDifference.magnitude (false :: bits) denominator.bits)
    have hmLength := SignedDifference.magnitude_length_le (false :: bits) denominator.bits
    dsimp [distance, ps, qs, mag]
    simp only [List.length_cons] at *
    omega
  · have hflag : t.val.registers 36 = e.val.registers 36 := by
      have hf36 := hff.2.2.2.2.2.2 36 (by omega) (by omega) (by omega) (by omega)
      have hg36 : g.val.registers 36 = f.val.registers 36 := by
        simp [g, Store.ofState, RewindOvershoot.finish, Rewind.finishAt]
      exact (htf.2.2.2.2.2.2 36 (by omega) (by omega)).trans (hg36.trans hf36)
    rw [hflag, heflag]
    have hv := SignedDifference.signed_value (false :: bits) denominator.bits
    have hs := SignedDifference.sign_iff (false :: bits) denominator.bits
    simp only [addressValue, Bool.toNat_false, zero_add, address_bits] at hv hs
    change (if SignedDifference.sign (false :: bits) denominator.bits then -(mag : ℤ)
      else (mag : ℤ)) = (2 * addressValue bits : ℕ) - (denominator : ℤ) at hv
    cases negative <;> cases hb : SignedDifference.sign (false :: bits) denominator.bits <;>
      simp_all <;> omega
  · have hg0 : g.val.tapes 0 = f.val.tapes 0 := by
      simp [g, Store.ofState, RewindOvershoot.finish, Rewind.finishAt]
    exact blank_of_eq ((htf.2.2.2.2.2.1 0 (by omega) (by omega)).trans hg0) hf0
  · have hg1 : g.val.tapes 1 = BitTape.shifted denominator.bits xo := by
      simpa only [g, Store.ofState, hdenPadded] using hrew.2
    exact (htf.2.2.2.2.2.1 1 (by omega) (by omega)).trans hg1

end Maxwell.Cost.SignedRound.Remainder
