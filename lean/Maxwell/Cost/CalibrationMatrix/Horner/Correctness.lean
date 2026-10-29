import Maxwell.Cost.CalibrationMatrix.Horner.Loop
import Maxwell.Cost.CalibrationMatrix.Horner.Semantics

namespace Maxwell.Cost.CalibrationMatrix.Horner
open Structured
open RationalAccumulator (Blank)

/-- The executed, uniform finite BitRAM loop returns the exact integer Horner
channels, including all array operations and all loop control costs. -/
theorem horner_channels {n : ℕ} (a : Snapshot n) (A : ChannelMatrix n) (D S : ℕ)
    (source : Channels n) (hdecode : a.Decodes A D S (source,source))
    (N B : ℕ) (hsized : a.data.Sized B) (hm : n*n < 2^B) (hn : n < 2^B)
    (hfit : ∀ k, k < N → Fits (a.iterate k).data (a.iterate k).words)
    (input : List Bool) (tape : ℕ → Bool) (count outer : List Bool)
    (hcount : addressValue count = n) (hcl : count.length ≤ B)
    (houter : addressValue outer = N) (hol : outer.length ≤ B)
    (origin : ℤ) (s : Store) (hs : a.Ready count B s.val)
    (h140 : s.val.tapes 140 = BitTape.shifted outer origin) :
    ∃ t : Store,
      (runPriced (code.compile.next input tape) (costCap N n B+1) s.val).finished =
        some (t.place code.size) ∧
      (runPriced (code.compile.next input tape) (costCap N n B+1) s.val).instructions ≤
        3600000*(N+1)*(n+1)^2*(B+2)^2 ∧
      (a.iterate N).Ready count B t.val ∧
      (a.iterate N).Decodes A D S (horner A D S source N) ∧
      (channels (a.iterate N).words 0 1,channels (a.iterate N).words 2 3) = horner A D S source N ∧
      Blank t.val 140 ∧ Frame s.val t.val ∧ Outside a.data s.val t.val := by
  obtain ⟨t,ht,hc,hr,hb,hfr,hmem⟩ := compiled_run a N B hsized hm hn hfit input tape count outer
    hcount hcl houter hol origin s hs h140
  exact ⟨t,ht,hc.trans (costCap_le N n B),hr,Snapshot.iterate_decodes hdecode N hfit,
    Snapshot.iterate_channels hdecode N hfit,hb,hfr,hmem⟩

end Maxwell.Cost.CalibrationMatrix.Horner
