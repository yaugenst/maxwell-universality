import Maxwell.Cost.CalibrationMatrix.PowerInvariant

namespace Maxwell.Cost.CalibrationMatrix
open Structured
open RationalAccumulator (Blank)
set_option maxHeartbeats 900000

def powerCode : Code := .seq (CountedShifted.code 140 powerStepCode) (.call (TapeOps.clear 140))

def powerCost (N n B : ℕ) : ℕ :=
  (N+1)*(13*B+15) + N*powerStepCost n B + 6*B+4

/-- A single uniform finite program iterates the actual dense signed
matrix product. Alternating buffer addresses are swapped by bit instructions;
there is no host continuation for a product or an iteration. -/
theorem power_executes {n : ℕ} (b : Buffers n) (N B : ℕ) (hsized : b.Sized B)
    (hsep : b.Separated) (hfit : ∀ k, k < N → (b.iterate k).Fits)
    (hm : n*n < 2^B) (hn : n < 2^B) (hW : 0 < addressValue b.data.width)
    (input : List Bool) (tape : ℕ → Bool) (count outer : List Bool)
    (hcount : addressValue count = n) (hcl : count.length ≤ B)
    (houter : addressValue outer = N) (hol : outer.length ≤ B)
    (origin : ℤ) (s : Store) (hs : b.Ready count B s.val)
    (h140 : s.val.tapes 140 = BitTape.shifted outer origin) :
    ∃ cost, ∃ t : Store, cost ≤ powerCost N n B ∧ Executes input tape powerCode cost s t ∧
      (b.iterate N).Ready count B t.val ∧ Blank t.val 140 ∧ PowerFrame s.val t.val ∧ b.Outside s.val t.val := by
  let inv := PowerInvariant b count N B s.val
  have stable : ∀ r a c, CountedShifted.Frame 140 a c → inv r a → inv r c :=
    power_invariant_stable b count N B s.val
  have bodyCorrect : ∀ r xs u, inv (r+1) u →
      u.val.tapes 140 = BitTape.shifted xs origin → addressValue xs = r →
      ∃ bodyCost t, Executes input tape powerStepCode bodyCost u t ∧ inv r t ∧
        t.val.tapes 140 = BitTape.shifted xs origin ∧ bodyCost ≤ powerStepCost n B := by
    intro r xs u hu hc _
    obtain ⟨hrem, hready, hfr, hmem⟩ := hu
    have hk : N-(r+1) < N := by omega
    obtain ⟨cost, t, hcost, he, htr, ht140, htf, htm⟩ :=
      power_step (b.iterate (N-(r+1))) B (hsized.iterate _) (hsep.iterate _) (hfit _ hk)
        hm hn (by simpa only [Buffers.iterate_width] using hW) input tape count hcount hcl u hready
    have hnext : N-r = N-(r+1)+1 := by omega
    refine ⟨cost, t, he, ⟨by omega, ?_, hfr.trans htf, ?_⟩, ht140.trans hc, hcost⟩
    · simpa only [hnext, Buffers.iterate] using htr
    · exact hmem.trans ((b.outside_iterate (N-(r+1)) u.val t.val).mp (Buffers.Outside.of_output htm))
  have initial : inv N s := by
    exact ⟨le_rfl, by simpa [inv, Buffers.iterate] using hs, PowerFrame.refl s.val, Buffers.Outside.refl b s.val⟩
  obtain ⟨cost, a, finalCount, he, haInv, haCount, haLen, _, haCost⟩ :=
    CountedShifted.executes 140 origin powerStepCode input tape inv (fun _ => powerStepCost n B)
      stable bodyCorrect N outer s houter h140 initial
  obtain ⟨_, har, haf, ham⟩ := haInv
  obtain ⟨t, et, ht, ft⟩ := WordCall.clear 140 input tape finalCount origin a haCount
  have keep (i : ℕ) (hi : i ≠ 140) : t.val.tapes i = a.val.tapes i := by simp [ht, hi]
  have frame : PowerFrame a.val t.val :=
    ⟨ft.2.1, ft.2.2.2.1, ft.2.2.2.2.1, fun i _ _ _ _ _ _ _ _ _ _ _ _ _ hi => keep i hi,
      fun i _ _ _ h26 h27 _ _ => ft.2.2.2.2.2.2 i h26 h27⟩
  refine ⟨cost+(6*finalCount.length+4), t, ?_, he.seq et, ?_,
    ⟨origin+finalCount.length, by simp [ht]⟩, haf.trans frame, ham.trans (Buffers.Outside.of_memory ft.2.2.1)⟩
  · simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at haCost
    have hlen : finalCount.length ≤ B := haLen.trans_le hol
    have hcounter : (N+1)*(13*outer.length+15) ≤ (N+1)*(13*B+15) := by gcongr
    dsimp [powerCost]
    omega
  · have hh := har.of_memory_tapes ft.2.2.1 keep
    simpa using hh

theorem power_compiled_run {n : ℕ} (b : Buffers n) (N B : ℕ) (hsized : b.Sized B)
    (hsep : b.Separated) (hfit : ∀ k, k < N → (b.iterate k).Fits)
    (hm : n*n < 2^B) (hn : n < 2^B) (hW : 0 < addressValue b.data.width)
    (input : List Bool) (tape : ℕ → Bool) (count outer : List Bool)
    (hcount : addressValue count = n) (hcl : count.length ≤ B)
    (houter : addressValue outer = N) (hol : outer.length ≤ B)
    (origin : ℤ) (s : Store) (hs : b.Ready count B s.val)
    (h140 : s.val.tapes 140 = BitTape.shifted outer origin) :
    ∃ t : Store,
      (runPriced (powerCode.compile.next input tape) (powerCost N n B+1) s.val).finished =
        some (t.place powerCode.size) ∧
      (runPriced (powerCode.compile.next input tape) (powerCost N n B+1) s.val).instructions ≤ powerCost N n B ∧
      (b.iterate N).Ready count B t.val ∧ Blank t.val 140 ∧ PowerFrame s.val t.val ∧ b.Outside s.val t.val := by
  obtain ⟨cost, t, hc, he, ht⟩ := power_executes b N B hsized hsep hfit hm hn hW input tape count outer
    hcount hcl houter hol origin s hs h140
  have hr := he.compiled_run (powerCost N n B+1) (by omega)
  exact ⟨t, hr.1, hr.2 ▸ hc, ht⟩

theorem powerStepCost_le (n B : ℕ) : powerStepCost n B ≤ 620000*(n+1)^2*(B+2)^2 := by
  have h := matvecCost_le n n B
  have hs : 100*B+100 ≤ 100*(B+2)^2 := by nlinarith
  dsimp [powerStepCost]
  nlinarith only [h, hs, Nat.zero_le ((10000*n^2+20000*n+9900)*(B+2)^2)]

theorem powerCost_le (N n B : ℕ) : powerCost N n B ≤ 630000*(N+1)*(n+1)^2*(B+2)^2 := by
  have hb : 13*B+15 ≤ 20*(B+2)^2 := by nlinarith
  have hs : 6*B+4 ≤ 10*(B+2)^2 := by nlinarith
  have h := Nat.mul_le_mul_left N (powerStepCost_le n B)
  calc
    _ ≤ (N+1)*(20*(B+2)^2)+N*(620000*(n+1)^2*(B+2)^2)+10*(B+2)^2 := by
      dsimp [powerCost]
      nlinarith only [h, Nat.mul_le_mul_left (N+1) hb, hs]
    _ ≤ _ := by
      nlinarith only [Nat.zero_le
        ((10000*N*n^2+20000*N*n+9980*N+630000*n^2+1260000*n+629970)*(B+2)^2)]

end Maxwell.Cost.CalibrationMatrix
