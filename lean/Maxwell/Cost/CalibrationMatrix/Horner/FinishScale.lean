import Maxwell.Cost.CalibrationMatrix.Horner.FinishSetup

namespace Maxwell.Cost.CalibrationMatrix.Horner
open Structured
open RationalAccumulator (Blank)
set_option maxHeartbeats 1200000

def finishScaleCode : Code := .seq (.call (WordTransfer.clone 107 108))
  (.seq Scale.code (.call (TapeOps.clear 104)))

def finishScaleCost (n B : ℕ) : ℕ := Scale.costBound n B+21*B+21

/-- The terminal scalar pass uses the same physical common scratch and
restores all row controls for the subsequent exact pairing pass. -/
theorem finish_scale {n : ℕ} (d : Scale.Data n) (words : Fin 4 → Vector (List Bool) n)
    (B : ℕ) (hsized : d.Sized B) (hn : n < 2^B)
    (hp : ∀ i, (Scale.positive d words i).bits.length ≤ addressValue d.width)
    (hneg : ∀ i, (Scale.negative d words i).bits.length ≤ addressValue d.width)
    (input : List Bool) (tape : ℕ → Bool) (count : List Bool)
    (hcount : addressValue count = n) (hcl : count.length ≤ B) (s : Store)
    (hw : WorkReady count B s.val) (hd : Scale.Stored d words s.val) :
    ∃ cost, ∃ t : Store, cost ≤ finishScaleCost n B ∧ Executes input tape finishScaleCode cost s t ∧
      WorkReady count B t.val ∧ Scale.Stored d (Scale.filledWords d words n) t.val ∧
      t.val.tapes 140 = s.val.tapes 140 ∧ MatrixFrame s.val t.val ∧
      Scale.Outside d s.val t.val := by
  obtain ⟨vi,hvi,hvl,hr,hi,h104,h107,h106,h37,h108,h109⟩ := hw
  obtain ⟨co,h107⟩ := h107
  obtain ⟨oo,h108⟩ := h108
  obtain ⟨a,ea,ha,fa⟩ := WordCall.clone 107 108 (by omega) input tape count co oo s h107 h108
  have keepA (i : ℕ) (hi : i ≠ 108) : a.val.tapes i = s.val.tapes i := by simp [ha,hi]
  have had := hd.of_tapes_memory fa.2.2.1 (fun i hi => keepA i (by omega))
  have frameA : MatrixFrame s.val a.val :=
    ⟨fa.2.1,fa.2.2.2.1,fa.2.2.2.2.1,fun i _ _ _ _ _ _ _ hi => keepA i hi,
      fun i _ h24 h25 h26 h27 _ _ => fa.2.2.2.2.2.2 i h24 h25 h26 h27⟩
  obtain ⟨steps,q,fi,hsteps,eq,hfi,hfil,hqi,hqd,hqr,hq37,hq108,hqcontrol,fq,hqm⟩ :=
    Scale.executes d words B hsized hn hp hneg input tape [] count rfl hcount (by simp) hcl oo a
      (hr.of_tapes (fun i hi => keepA i (by omega))) had
      (BankArray.word_of_eq (keepA 104 (by omega)) h104)
      (RationalAccumulator.blank_of_eq (keepA 37 (by omega)) h37) (by simp [ha])
  obtain ⟨fo,hqi⟩ := hqi
  obtain ⟨t,et,ht,ft⟩ := WordCall.clear 104 input tape fi fo q hqi
  have keepT (i : ℕ) (hi : i ≠ 104) : t.val.tapes i = q.val.tapes i := by simp [ht,hi]
  have frameT : MatrixFrame q.val t.val :=
    ⟨ft.2.1,ft.2.2.2.1,ft.2.2.2.2.1,fun i _ _ _ _ _ hi _ _ => keepT i hi,
      fun i _ _ _ h26 h27 _ _ => ft.2.2.2.2.2.2 i h26 h27⟩
  have keepQ (i : ℕ) (hi : i = 107 ∨ i = 109 ∨ 110 ≤ i) : q.val.tapes i = a.val.tapes i :=
    fq.2.2.2.1 i (Or.inr (by omega)) (Or.inr (by omega)) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega)
  have kept (i : ℕ) (hi : i = 107 ∨ i = 109 ∨ 110 ≤ i) : t.val.tapes i = s.val.tapes i :=
    (keepT i (by omega)).trans ((keepQ i hi).trans (keepA i (by omega)))
  refine ⟨15*count.length+17+(steps+(6*fi.length+4)),t,?_,ea.seq (eq.seq et),?_,
    hqd.of_tapes_memory ft.2.2.1 (fun i hi => keepT i (by omega)),
    kept 140 (by omega),((frameA.trans fq).trans frameT),
    (Scale.Outside.of_memory fa.2.2.1).trans (hqm.trans (Scale.Outside.of_memory ft.2.2.1))⟩
  · dsimp [finishScaleCost];omega
  · refine ⟨vi,hvi,hvl,hqr.of_tapes (fun i hi => keepT i (by omega)),
      ⟨BankArray.word_of_eq ((keepT 102 (by omega)).trans ((hqcontrol 102 (by omega)).trans (keepA 102 (by omega)))) hi.1,
        BankArray.word_of_eq ((keepT 103 (by omega)).trans ((hqcontrol 103 (by omega)).trans (keepA 103 (by omega)))) hi.2⟩,
      ⟨fo+fi.length,by simp [ht,BitTape.shifted,BitTape.blank]⟩,
      ⟨co,(kept 107 (by omega)).trans h107⟩,
      RationalAccumulator.blank_of_eq ((keepT 106 (by omega)).trans ((hqcontrol 106 (by omega)).trans (keepA 106 (by omega)))) h106,
      RationalAccumulator.blank_of_eq (keepT 37 (by omega)) hq37,
      RationalAccumulator.blank_of_eq (keepT 108 (by omega)) hq108,
      RationalAccumulator.blank_of_eq (kept 109 (by omega)) h109⟩

end Maxwell.Cost.CalibrationMatrix.Horner
