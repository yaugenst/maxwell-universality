import Maxwell.Cost.CalibrationMatrix.Horner.Finish
import Maxwell.Cost.CalibrationMatrix.Horner.Width

namespace Maxwell.Cost.CalibrationMatrix.Horner
open Structured
open RationalAccumulator (Blank)
set_option maxHeartbeats 1200000

def inverseCode : Code := .seq code finishCode
def inverseCost (N n B : ℕ) : ℕ := costCap N n B+finishCost n B

theorem finish_fits_of_bits {n : ℕ} {a : Snapshot n} {A : ChannelMatrix n}
    {D S : ℕ} {state : Channels n × Channels n} (hd : a.Decodes A D S state)
    (hprod : FitsWidth (addressValue a.data.width) (matvec A state.2))
    (hscale : FitsWidth (addressValue a.data.width) ((matvec A state.2).scale S)) :
    (a.data.productBuffers a.words 2 3 10 11).Fits ∧
    (∀ i, (Scale.positive a.data.finishData (finishWords (firstWords a.data a.words)) i).bits.length ≤ addressValue a.data.width) ∧
    (∀ i, (Scale.negative a.data.finishData (finishWords (firstWords a.data a.words)) i).bits.length ≤ addressValue a.data.width) := by
  have dec : (a.data.productData a.words 2 3).Decodes A state.2 := by
    simpa only [hd.value] using hd.matrix.product a.words 2 3
  have hf : (a.data.productBuffers a.words 2 3 10 11).Fits :=
    Buffers.fits_of_decodes dec hprod.1 hprod.2
  have hh : channels (firstWords a.data a.words) 10 11 = matvec A state.2 := by
    rw [firstWords,product_channels hd.matrix _ _ _ _ _ (by decide) hf,hd.value]
  have hp i := congrArg (fun c : Channels n => c.positive i) hh
  have hn i := congrArg (fun c : Channels n => c.negative i) hh
  simp only [channels] at hp hn
  refine ⟨hf,?_,?_⟩
  · intro i
    change (addressValue (((firstWords a.data a.words) 10).get i)*a.data.S).bits.length ≤ _
    rw [hp i,hd.numerator]
    simpa only [Channels.scale,Nat.mul_comm] using hscale.1 i
  · intro i
    change (addressValue (((firstWords a.data a.words) 11).get i)*a.data.S).bits.length ≤ _
    rw [hn i,hd.numerator]
    simpa only [Channels.scale,Nat.mul_comm] using hscale.2 i

theorem inverseCost_le (N n B : ℕ) : inverseCost N n B ≤ 5000000*(N+1)*(n+1)^2*(B+2)^2 := by
  have h := costCap_le N n B
  have hf := finishCost_le n B
  dsimp [inverseCost]
  nlinarith only [h,hf,Nat.zero_le (1400000*N*(n+1)^2*(B+2)^2)]

/-- A fixed finite program computes the full division-free inverse numerator.
The premises bound only the exact mathematical integer channels; all indexed
matrix products, affine passes, loops, descriptor copies and cleanup execute
on the bit machine. The output pair is on descriptor tapes128/129. -/
theorem inverse_executes {n : ℕ} (a : Snapshot n) (A : ChannelMatrix n) (D S : ℕ)
    (source : Channels n) (hdecode : a.Decodes A D S (source,source))
    (N B : ℕ) (hsized : a.data.Sized B) (hm : n*n < 2^B) (hn : n < 2^B)
    (h1 : ∀ k, k < N → FitsWidth (addressValue a.data.width) (matvec A (horner A D S source k).2))
    (h2 : ∀ k, k < N → FitsWidth (addressValue a.data.width) (matvec A (matvec A (horner A D S source k).2)))
    (hw : ∀ k, k < N → FitsWidth (addressValue a.data.width) (horner A D S source (k+1)).1)
    (hx : ∀ k, k < N → FitsWidth (addressValue a.data.width) (horner A D S source (k+1)).2)
    (hprod : FitsWidth (addressValue a.data.width) (matvec A (horner A D S source N).2))
    (hscale : FitsWidth (addressValue a.data.width) (inverseNumerator A D S source N))
    (input : List Bool) (tape : ℕ → Bool) (count outer : List Bool)
    (hcount : addressValue count = n) (hcl : count.length ≤ B)
    (houter : addressValue outer = N) (hol : outer.length ≤ B)
    (origin : ℤ) (s : Store) (hs : a.Ready count B s.val)
    (h140 : s.val.tapes 140 = BitTape.shifted outer origin) :
    ∃ cost, ∃ t : Store, cost ≤ inverseCost N n B ∧
      Executes input tape inverseCode cost s t ∧
      WorkReady count B t.val ∧
      Scale.Stored (a.iterate N).data.finishData (finishResult (a.iterate N).data (a.iterate N).words) t.val ∧
      Ports (a.iterate N).data 10 11 2 3 t.val ∧
      Scale.channels (finishResult (a.iterate N).data (a.iterate N).words) 2 3 = inverseNumerator A D S source N ∧
      Blank t.val 140 ∧ FinishFrame s.val t.val ∧ Outside a.data s.val t.val := by
  have hfit := Snapshot.iterate_fits_of_bits hdecode N h1 h2 hw hx
  have hd := Snapshot.iterate_decodes hdecode N hfit
  obtain ⟨hf,hp,hneg⟩ := finish_fits_of_bits hd
    (by simpa only [Snapshot.iterate_width] using hprod)
    (by simpa only [Snapshot.iterate_width,inverseNumerator] using hscale)
  obtain ⟨c1,b,hc1,eb,hbr,hb140,fb,mb⟩ := executes a N B hsized hm hn hfit input tape count outer
    hcount hcl houter hol origin s hs h140
  obtain ⟨c2,t,hc2,et,htw,htd,htports,ht140,ft,mt⟩ := finish (a.iterate N) B (a.iterate_sized hsized N)
    hm hn hf hp hneg input tape count hcount hcl b hbr
  have he : Executes input tape inverseCode (c1+c2) s t := eb.seq et
  have hc : c1+c2 ≤ inverseCost N n B := by dsimp [inverseCost];omega
  exact ⟨c1+c2,t,hc,he,htw,htd,htports,
    finish_result_channels hd hf hp hneg,RationalAccumulator.blank_of_eq ht140 hb140,
    (FinishFrame.of_horner fb).trans ft,mb.trans ((a.iterate_outside N b.val t.val).mp mt)⟩

theorem inverse_channels {n : ℕ} (a : Snapshot n) (A : ChannelMatrix n) (D S : ℕ)
    (source : Channels n) (hdecode : a.Decodes A D S (source,source))
    (N B : ℕ) (hsized : a.data.Sized B) (hm : n*n < 2^B) (hn : n < 2^B)
    (h1 : ∀ k, k < N → FitsWidth (addressValue a.data.width) (matvec A (horner A D S source k).2))
    (h2 : ∀ k, k < N → FitsWidth (addressValue a.data.width) (matvec A (matvec A (horner A D S source k).2)))
    (hw : ∀ k, k < N → FitsWidth (addressValue a.data.width) (horner A D S source (k+1)).1)
    (hx : ∀ k, k < N → FitsWidth (addressValue a.data.width) (horner A D S source (k+1)).2)
    (hprod : FitsWidth (addressValue a.data.width) (matvec A (horner A D S source N).2))
    (hscale : FitsWidth (addressValue a.data.width) (inverseNumerator A D S source N))
    (input : List Bool) (tape : ℕ → Bool) (count outer : List Bool)
    (hcount : addressValue count = n) (hcl : count.length ≤ B)
    (houter : addressValue outer = N) (hol : outer.length ≤ B)
    (origin : ℤ) (s : Store) (hs : a.Ready count B s.val)
    (h140 : s.val.tapes 140 = BitTape.shifted outer origin) :
    ∃ t : Store,
      (runPriced (inverseCode.compile.next input tape) (inverseCost N n B+1) s.val).finished =
        some (t.place inverseCode.size) ∧
      (runPriced (inverseCode.compile.next input tape) (inverseCost N n B+1) s.val).instructions ≤
        5000000*(N+1)*(n+1)^2*(B+2)^2 ∧
      WorkReady count B t.val ∧
      Scale.Stored (a.iterate N).data.finishData (finishResult (a.iterate N).data (a.iterate N).words) t.val ∧
      Ports (a.iterate N).data 10 11 2 3 t.val ∧
      Scale.channels (finishResult (a.iterate N).data (a.iterate N).words) 2 3 = inverseNumerator A D S source N ∧
      Blank t.val 140 ∧ FinishFrame s.val t.val ∧ Outside a.data s.val t.val := by
  obtain ⟨cost,t,hc,he,ht⟩ := inverse_executes a A D S source hdecode N B hsized hm hn
    h1 h2 hw hx hprod hscale input tape count outer hcount hcl houter hol origin s hs h140
  have hr := he.compiled_run (inverseCost N n B+1) (by omega)
  exact ⟨t,hr.1,hr.2 ▸ hc.trans (inverseCost_le N n B),ht⟩

end Maxwell.Cost.CalibrationMatrix.Horner
