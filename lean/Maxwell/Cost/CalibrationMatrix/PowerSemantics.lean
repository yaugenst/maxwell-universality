import Maxwell.Cost.CalibrationMatrix.Power

namespace Maxwell.Cost.CalibrationMatrix
open Structured
open RationalAccumulator (Blank)

theorem Buffers.fits_of_decodes {n : ℕ} {b : Buffers n} {A : ChannelMatrix n} {x : Channels n}
    (h : b.data.Decodes A x)
    (hp : ∀ i, ((matvec A x).positive i).bits.length ≤ addressValue b.data.width)
    (hn : ∀ i, ((matvec A x).negative i).bits.length ≤ addressValue b.data.width) : b.Fits :=
  ⟨fun i => by simpa only [b.data.outputPositive_eq_matvec h i] using hp i,
    fun i => by simpa only [b.data.outputNegative_eq_matvec h i] using hn i⟩

/-- The finite word-width premise is stated directly for the exact integer
power sequence, and implies every actual alternating-buffer write fits. -/
theorem Buffers.iterate_fits_of_bits {n : ℕ} {b : Buffers n} {A : ChannelMatrix n} {x : Channels n}
    (h : b.data.Decodes A x) (N : ℕ)
    (hp : ∀ k, k ≤ N → ∀ i, ((matrixPower A x k).positive i).bits.length ≤ addressValue b.data.width)
    (hn : ∀ k, k ≤ N → ∀ i, ((matrixPower A x k).negative i).bits.length ≤ addressValue b.data.width) :
    (∀ k, k < N → (b.iterate k).Fits) ∧ (b.iterate N).data.Decodes A (matrixPower A x N) := by
  have decodes : ∀ k, k ≤ N → (b.iterate k).data.Decodes A (matrixPower A x k) := by
    intro k
    induction k with
    | zero => intro _; exact h
    | succ k ih =>
      intro hk
      have hd := ih (by omega)
      have hf : (b.iterate k).Fits := Buffers.fits_of_decodes hd
        (fun i => by simpa only [Buffers.iterate_width, matrixPower] using hp (k+1) hk i)
        (fun i => by simpa only [Buffers.iterate_width, matrixPower] using hn (k+1) hk i)
      exact (b.iterate k).advance_decodes hd hf
  refine ⟨?_, decodes N le_rfl⟩
  intro k hk
  exact Buffers.fits_of_decodes (decodes k (by omega))
    (fun i => by simpa only [Buffers.iterate_width, matrixPower] using hp (k+1) (by omega) i)
    (fun i => by simpa only [Buffers.iterate_width, matrixPower] using hn (k+1) (by omega) i)

/-- Exact signed integer powers, realized by the concrete finite BitRAM
program, with the physical input, scratch, frames and size premises exposed. -/
theorem power_channels {n : ℕ} (b : Buffers n) (A : ChannelMatrix n) (x : Channels n)
    (hdecode : b.data.Decodes A x) (N B : ℕ) (hsized : b.Sized B) (hsep : b.Separated)
    (hp : ∀ k, k ≤ N → ∀ i, ((matrixPower A x k).positive i).bits.length ≤ addressValue b.data.width)
    (hneg : ∀ k, k ≤ N → ∀ i, ((matrixPower A x k).negative i).bits.length ≤ addressValue b.data.width)
    (hm : n*n < 2^B) (hn : n < 2^B) (hW : 0 < addressValue b.data.width)
    (input : List Bool) (tape : ℕ → Bool) (count outer : List Bool)
    (hcount : addressValue count = n) (hcl : count.length ≤ B)
    (houter : addressValue outer = N) (hol : outer.length ≤ B)
    (origin : ℤ) (s : Store) (hs : b.Ready count B s.val)
    (h140 : s.val.tapes 140 = BitTape.shifted outer origin) :
    ∃ t : Store,
      (runPriced (powerCode.compile.next input tape) (powerCost N n B+1) s.val).finished =
        some (t.place powerCode.size) ∧
      (runPriced (powerCode.compile.next input tape) (powerCost N n B+1) s.val).instructions ≤
        630000*(N+1)*(n+1)^2*(B+2)^2 ∧
      (b.iterate N).Ready count B t.val ∧ (b.iterate N).data.Decodes A (matrixPower A x N) ∧
      Blank t.val 140 ∧ PowerFrame s.val t.val ∧ b.Outside s.val t.val := by
  obtain ⟨hf, hd⟩ := Buffers.iterate_fits_of_bits hdecode N hp hneg
  obtain ⟨t, ht, hc, hr, hb, hfr, hm⟩ := power_compiled_run b N B hsized hsep hf hm hn hW
    input tape count outer hcount hcl houter hol origin s hs h140
  exact ⟨t, ht, hc.trans (powerCost_le N n B), hr, hd, hb, hfr, hm⟩

end Maxwell.Cost.CalibrationMatrix
