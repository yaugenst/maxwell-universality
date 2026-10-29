import Maxwell.Cost.DecoderAddressWidth.Fetch
import Maxwell.Cost.DecoderParser.Term

namespace Maxwell.Cost.DecoderAddressWidth
open Structured DecoderParser
open RationalAccumulator (Bank Scratch Word Blank)
set_option maxRecDepth 8192

/-- Uniform fetch width, determined solely by the stored format and number
of samples; message values and rational coefficients do not enter it. -/
def fetchWidth {ι : Type*} {n : ℕ} (D : Target.WeightedDecoder ι n) : ℕ :=
  D.format.width.bits.length+D.sampleCount.bits.length+1+D.format.width

theorem term_visited {ι : Type*} {n : ℕ} (D : Target.WeightedDecoder ι n)
    (j : Fin D.sampleCount) (q : ℚ) (preceding suffix : List Bool) (tape : ℕ→Bool)
    (W : ℕ) (hW : fetchWidth D ≤ W) (s t : Store)
    (hs : Address.Within W s.val) (hh : s.val.inputHead=preceding.length)
    (hr : EvalReady D.format s.val) (cost : ℕ)
    (run : Executes (preceding++(Codec.nat j.val++(Codec.rat q++suffix))) tape termCode cost s t) :
    Visited W (preceding++(Codec.nat j.val++(Codec.rat q++suffix))) tape termCode cost s t := by
  let input := preceding++(Codec.nat j.val++(Codec.rat q++suffix))
  obtain ⟨u,eu,huh,hu45,hu10,huf⟩ := readNatural_steps 45 (by decide) j.val preceding
    (Codec.rat q++suffix) tape s hh (hr.parser 10 (by decide)) (hr.parser 45 (by decide))
  obtain ⟨a,ea,_,_,_,_,_,haf⟩ := readRational_steps q
    (preceding++Codec.nat j.val) suffix tape u (by simp [huh,hh]) hu10
    ((huf.tapes 12 (by decide)).trans (hr.parser 12 (by decide)))
    ((huf.tapes 13 (by decide)).trans (hr.parser 13 (by decide)))
  have hieq : (preceding++Codec.nat j.val)++(Codec.rat q++suffix)=input := by simp [input,List.append_assoc]
  rw [hieq] at ea
  have hap : DecoderParser.Frame {45,12,13} s.val a.val :=
    (huf.mono (by simp)).trans (haf.mono (by simp))
  have ha45 : a.val.tapes 45=BitTape.ofList j.val.bits := (haf.tapes 45 (by decide)).trans hu45
  have har : Scratch a.val 0 := hap.scratch (by intro i hi;simp;omega) hr.arithmetic
  have haextra (i : ℕ) (hi : i ∈ ({5,6,7,8,9,65} : Finset ℕ)) : Blank a.val i :=
    RationalAccumulator.blank_of_eq (hap.tapes i (by
      simp only [Finset.mem_insert,Finset.mem_singleton] at hi ⊢;omega)) (hr.blank i hi)
  obtain ⟨wo,hwo⟩ := hr.width
  obtain ⟨co,hco⟩ := hr.center
  have hascratch : DecoderFetch.Scratch a.val :=
    ⟨har.1,(RationalAccumulator.zero_word_iff_blank _ _).mp har.2.1,har.2.2.1,har.2.2.2,
      haextra 5 (by decide),haextra 6 (by decide),haextra 8 (by decide),haextra 9 (by decide)⟩
  have hwidth : 0 < D.format.width.bits.length := RationalAccumulator.bits_nonempty
    (by simp [Target.FixedPointFormat.width])
  have hclock : (2^(D.format.integerBits+D.format.fractionalBits)).bits.length=D.format.width := by
    rw [Nat.size_eq_bits_len,Nat.size_pow]
    simp [Target.FixedPointFormat.width,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]
  have hj : j.val.bits.length ≤ D.sampleCount.bits.length := by
    simp only [Nat.size_eq_bits_len]
    exact Nat.size_le_size (Nat.le_of_lt j.isLt)
  have eU : Visited W input tape (readNatural 45) _ s u := eu.visited_noAddressPush (by decide) hs
  have eA : Visited W input tape readRational _ u a := ea.visited_noAddressPush (by decide) eU.finish
  change Executes input tape (.seq _ (.seq _ (.seq _ _))) cost s t at run
  cases run with
  | seq first rest =>
    rcases eu.deterministic first with ⟨rfl,rfl⟩
    cases rest with
    | seq second rest =>
      rcases ea.deterministic second with ⟨rfl,rfl⟩
      cases rest with
      | seq fetching tail =>
        have hF := fetch_visited input tape D.format.width.bits j.val.bits
          (2^(D.format.integerBits+D.format.fractionalBits)).bits wo 0 co hwidth a _ hascratch
          ((hap.tapes 64 (by decide)).trans hwo)
          (by simpa [BitTape.shifted,BitTape.ofList] using ha45)
          ((hap.tapes 66 (by decide)).trans hco) _ fetching
        have hF' : Visited W input tape DecoderFetch.code _ _ _ := hF.mono (by
          apply max_le eA.finish
          rw [hclock]
          exact (by dsimp [fetchWidth] at hW;omega))
        exact eU.seq (eA.seq (hF'.seq (tail.visited_noAddressPush (by decide) hF'.finish)))

end Maxwell.Cost.DecoderAddressWidth
