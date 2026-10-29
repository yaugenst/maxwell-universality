import Maxwell.Cost.CalibrationMatrix.Horner.FinishScale

namespace Maxwell.Cost.CalibrationMatrix.Horner
open Structured
set_option maxHeartbeats 1200000

def finishCode : Code := .seq powerStepCode (.seq finishSetupCode finishScaleCode)
def finishCost (n B : ℕ) : ℕ := powerStepCost n B+finishScaleCost n B+63*B+63

def finishResult {n : ℕ} (d : Data n) (words : Fin 12 → Vector (List Bool) n) :=
  Scale.filledWords d.finishData (finishWords (firstWords d words)) n

theorem Outside.of_scale {n : ℕ} {d : Data n} {s t : BitRAMState}
    (h : Scale.Outside d.finishData s t) : Outside d s t :=
  fun a ha => h a (fun i _ => ha (finishPort i))

/-- One final physical matrix product and scalar pass produce the numerator
of the finite inverse polynomial in the output arrays128/129. -/
theorem finish {n : ℕ} (a : Snapshot n) (B : ℕ) (hsized : a.data.Sized B)
    (hm : n*n < 2^B) (hn : n < 2^B)
    (hfit : (a.data.productBuffers a.words 2 3 10 11).Fits)
    (hp : ∀ i, (Scale.positive a.data.finishData (finishWords (firstWords a.data a.words)) i).bits.length ≤ addressValue a.data.width)
    (hneg : ∀ i, (Scale.negative a.data.finishData (finishWords (firstWords a.data a.words)) i).bits.length ≤ addressValue a.data.width)
    (input : List Bool) (tape : ℕ → Bool) (count : List Bool)
    (hcount : addressValue count = n) (hcl : count.length ≤ B) (s : Store)
    (hs : a.Ready count B s.val) :
    ∃ cost, ∃ t : Store, cost ≤ finishCost n B ∧ Executes input tape finishCode cost s t ∧
      WorkReady count B t.val ∧ Scale.Stored a.data.finishData (finishResult a.data a.words) t.val ∧
      Ports a.data 10 11 2 3 t.val ∧
      t.val.tapes 140 = s.val.tapes 140 ∧ FinishFrame s.val t.val ∧ Outside a.data s.val t.val := by
  obtain ⟨c1,b,hc1,eb,hbW,hbD,hbP,hb140,fb,mb⟩ := multiply a.data a.words 2 3 10 11
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    B hsized hm hn hfit input tape count hcount hcl s hs.1 hs.2.1 hs.2.2
  obtain ⟨c,ec,hcW,hcD,hc140,mc,kc,fc,hcost⟩ := finish_setup a.data (firstWords a.data a.words)
    B hsized input tape count b hbW hbD
  obtain ⟨c3,t,hc3,et,htW,htD,ht140,ft,mt⟩ := finish_scale a.data.finishData
    (finishWords (firstWords a.data a.words)) B (Data.finish_sized hsized) hn hp hneg
    input tape count hcount hcl c hcW hcD
  refine ⟨c1+(_+c3),t,?_,eb.seq (ec.seq et),htW,htD,?_,ht140.trans (hc140.trans hb140),
    ((FinishFrame.of_horner (Frame.of_power fb)).trans fc).trans (FinishFrame.of_horner (Frame.of_power (CalibrationMatrix.PowerFrame.of_matrix ft))),
    ((Outside.of_output mb).trans (Outside.of_memory mc)).trans (Outside.of_scale mt)⟩
  · dsimp [finishCost]
    omega
  · have keep (i : ℕ) (hi : 110 ≤ i) : t.val.tapes i = c.val.tapes i :=
      ft.2.2.2.1 i (Or.inr (by omega)) (Or.inr (by omega)) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega)
    exact ⟨BankArray.word_of_eq ((keep 112 (by omega)).trans (kc 112 (by omega) (by omega) (by omega))) hbP.inputPositive,
      BankArray.word_of_eq ((keep 113 (by omega)).trans (kc 113 (by omega) (by omega) (by omega))) hbP.inputNegative,
      BankArray.word_of_eq ((keep 114 (by omega)).trans (kc 114 (by omega) (by omega) (by omega))) hbP.outputPositive,
      BankArray.word_of_eq ((keep 115 (by omega)).trans (kc 115 (by omega) (by omega) (by omega))) hbP.outputNegative⟩

/-- The serialized arrays produced by the terminal pass decode the exact
signed numerator, with no cancellation or reduction assumption. -/
theorem finish_result_channels {n : ℕ} {a : Snapshot n} {A : ChannelMatrix n}
    {D S : ℕ} {state : Channels n × Channels n} (hd : a.Decodes A D S state)
    (hfit : (a.data.productBuffers a.words 2 3 10 11).Fits)
    (hp : ∀ i, (Scale.positive a.data.finishData (finishWords (firstWords a.data a.words)) i).bits.length ≤ addressValue a.data.width)
    (hneg : ∀ i, (Scale.negative a.data.finishData (finishWords (firstWords a.data a.words)) i).bits.length ≤ addressValue a.data.width) :
    Scale.channels (finishResult a.data a.words) 2 3 = (matvec A state.2).scale S := by
  have hh := Scale.filled_channels a.data.finishData (finishWords (firstWords a.data a.words)) hp hneg
  change Scale.channels (finishResult a.data a.words) 2 3 =
    (channels (firstWords a.data a.words) 10 11).scale a.data.S at hh
  rw [firstWords,product_channels hd.matrix _ _ _ _ _ (by decide) hfit,hd.value,hd.numerator] at hh
  exact hh

theorem finishCost_le (n B : ℕ) : finishCost n B ≤ 1400000*(n+1)^2*(B+2)^2 := by
  have hp := powerStepCost_le n B
  have hs := Scale.costBound_le n B
  have hn : n+1 ≤ (n+1)^2 := by nlinarith
  have hs' : Scale.costBound n B ≤ 750000*(n+1)^2*(B+2)^2 := hs.trans (by gcongr)
  have hb : 84*B+84 ≤ 100*(B+2)^2 := by nlinarith
  dsimp [finishCost,finishScaleCost]
  nlinarith only [hp,hs',hb,Nat.zero_le ((30000*n^2+60000*n+29900)*(B+2)^2)]

end Maxwell.Cost.CalibrationMatrix.Horner
