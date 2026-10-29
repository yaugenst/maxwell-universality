import Maxwell.Cost.CalibrationMatrix.Horner.Multiply
import Maxwell.Cost.CalibrationMatrix.Assign

namespace Maxwell.Cost.CalibrationMatrix.Horner
open Structured

/-- These are precisely the small scratch tapes and cursor words carried
between the matrix and affine passes. -/
def WorkTape (i : ℕ) : Prop := i < 10 ∨ (30 ≤ i ∧ i ≤ 37) ∨ (102 ≤ i ∧ i ≤ 109)

theorem WorkReady.of_tapes {count : List Bool} {B : ℕ} {s t : BitRAMState}
    (h : WorkReady count B s) (keep : ∀ i, WorkTape i → t.tapes i = s.tapes i) : WorkReady count B t := by
  obtain ⟨vi,hvi,hvl,hr,hi,h104,h107,h106,h37,h108,h109⟩ := h
  exact ⟨vi,hvi,hvl,hr.of_tapes (fun i hi => keep i (by dsimp [WorkTape]; omega)),
    ⟨BankArray.word_of_eq (keep 102 (by simp [WorkTape])) hi.1,
      BankArray.word_of_eq (keep 103 (by simp [WorkTape])) hi.2⟩,
    BankArray.word_of_eq (keep 104 (by simp [WorkTape])) h104,
    BankArray.word_of_eq (keep 107 (by simp [WorkTape])) h107,
    RationalAccumulator.blank_of_eq (keep 106 (by simp [WorkTape])) h106,
    RationalAccumulator.blank_of_eq (keep 37 (by simp [WorkTape])) h37,
    RationalAccumulator.blank_of_eq (keep 108 (by simp [WorkTape])) h108,
    RationalAccumulator.blank_of_eq (keep 109 (by simp [WorkTape])) h109⟩

def selectOutputCode (p q : Fin 12) : Code := .seq (Assign.code (baseBank p) 114) (Assign.code (baseBank q) 115)

theorem select_output {n : ℕ} (d : Data n) (words : Fin 12 → Vector (List Bool) n)
    (ip iq op oq p q : Fin 12) (B : ℕ) (hsized : d.Sized B)
    (input : List Bool) (tape : ℕ → Bool) (count : List Bool) (s : Store)
    (hw : WorkReady count B s.val) (hd : Stored d words s.val) (hp : Ports d ip iq op oq s.val) :
    ∃ cost, ∃ t : Store, cost ≤ 42*B+42 ∧ Executes input tape (selectOutputCode p q) cost s t ∧
      WorkReady count B t.val ∧ Stored d words t.val ∧ Ports d ip iq p q t.val ∧
      t.val.tapes 140 = s.val.tapes 140 ∧ t.val.memory = s.val.memory ∧ CalibrationMatrix.PowerFrame s.val t.val := by
  obtain ⟨a,ea,ha114,keepA,fa⟩ := Assign.executes (baseBank p) 114 (by have := baseBank_bounds p; omega)
    input tape (d.bases p) (d.bases op) s (hd.bases p) hp.outputPositive
  obtain ⟨t,et,ht115,keepT,ft⟩ := Assign.executes (baseBank q) 115 (by have := baseBank_bounds q; omega)
    input tape (d.bases q) (d.bases oq) a
      (BankArray.word_of_eq (keepA _ (by have := baseBank_bounds q; omega)) (hd.bases q))
      (BankArray.word_of_eq (keepA 115 (by omega)) hp.outputNegative)
  have keep (i : ℕ) (hi : i ≠ 114) (hj : i ≠ 115) : t.val.tapes i = s.val.tapes i :=
    (keepT i hj).trans (keepA i hi)
  have hmem := ft.2.2.1.trans fa.2.2.1
  refine ⟨(6*(d.bases op).length+4+(15*(d.bases p).length+17))+
      (6*(d.bases oq).length+4+(15*(d.bases q).length+17)),t,?_,ea.seq et,
    hw.of_tapes (fun i hi => keep i (by dsimp [WorkTape] at hi; omega) (by dsimp [WorkTape] at hi; omega)),
    hd.of_memory_tapes hmem (fun i hi => keep i (by dsimp [Metadata] at hi; omega) (by dsimp [Metadata] at hi; omega)),
    ⟨BankArray.word_of_eq (keep 112 (by omega) (by omega)) hp.inputPositive,
      BankArray.word_of_eq (keep 113 (by omega) (by omega)) hp.inputNegative,
      BankArray.word_of_eq (keepT 114 (by omega)) ha114,ht115⟩,
    keep 140 (by omega) (by omega),hmem,?_⟩
  · have hp := hsized.2.2.2.2.1 p
    have hq := hsized.2.2.2.2.1 q
    have hop := hsized.2.2.2.2.1 op
    have hoq := hsized.2.2.2.2.1 oq
    omega
  · exact ⟨ft.2.1.trans fa.2.1,ft.2.2.2.1.trans fa.2.2.2.1,ft.2.2.2.2.1.trans fa.2.2.2.2.1,
      fun i _ _ _ _ _ _ _ _ _ _ _ hi hj _ => keep i hi hj,
      fun i _ h24 h25 h26 h27 _ _ => (ft.2.2.2.2.2.2 i h24 h25 h26 h27).trans (fa.2.2.2.2.2.2 i h24 h25 h26 h27)⟩

def selectInputCode (p q : Fin 12) : Code := .seq (Assign.code (baseBank p) 112) (Assign.code (baseBank q) 113)

theorem select_input {n : ℕ} (d : Data n) (words : Fin 12 → Vector (List Bool) n)
    (ip iq op oq p q : Fin 12) (B : ℕ) (hsized : d.Sized B)
    (input : List Bool) (tape : ℕ → Bool) (count : List Bool) (s : Store)
    (hw : WorkReady count B s.val) (hd : Stored d words s.val) (hp : Ports d ip iq op oq s.val) :
    ∃ cost, ∃ t : Store, cost ≤ 42*B+42 ∧ Executes input tape (selectInputCode p q) cost s t ∧
      WorkReady count B t.val ∧ Stored d words t.val ∧ Ports d p q op oq t.val ∧
      t.val.tapes 140 = s.val.tapes 140 ∧ t.val.memory = s.val.memory ∧ CalibrationMatrix.PowerFrame s.val t.val := by
  obtain ⟨a,ea,ha112,keepA,fa⟩ := Assign.executes (baseBank p) 112 (by have := baseBank_bounds p; omega)
    input tape (d.bases p) (d.bases ip) s (hd.bases p) hp.inputPositive
  obtain ⟨t,et,ht113,keepT,ft⟩ := Assign.executes (baseBank q) 113 (by have := baseBank_bounds q; omega)
    input tape (d.bases q) (d.bases iq) a
      (BankArray.word_of_eq (keepA _ (by have := baseBank_bounds q; omega)) (hd.bases q))
      (BankArray.word_of_eq (keepA 113 (by omega)) hp.inputNegative)
  have keep (i : ℕ) (hi : i ≠ 112) (hj : i ≠ 113) : t.val.tapes i = s.val.tapes i :=
    (keepT i hj).trans (keepA i hi)
  have hmem := ft.2.2.1.trans fa.2.2.1
  refine ⟨(6*(d.bases ip).length+4+(15*(d.bases p).length+17))+
      (6*(d.bases iq).length+4+(15*(d.bases q).length+17)),t,?_,ea.seq et,
    hw.of_tapes (fun i hi => keep i (by dsimp [WorkTape] at hi; omega) (by dsimp [WorkTape] at hi; omega)),
    hd.of_memory_tapes hmem (fun i hi => keep i (by dsimp [Metadata] at hi; omega) (by dsimp [Metadata] at hi; omega)),
    ⟨BankArray.word_of_eq (keepT 112 (by omega)) ha112,ht113,
      BankArray.word_of_eq (keep 114 (by omega) (by omega)) hp.outputPositive,
      BankArray.word_of_eq (keep 115 (by omega) (by omega)) hp.outputNegative⟩,
    keep 140 (by omega) (by omega),hmem,?_⟩
  · have hp := hsized.2.2.2.2.1 p
    have hq := hsized.2.2.2.2.1 q
    have hop := hsized.2.2.2.2.1 ip
    have hoq := hsized.2.2.2.2.1 iq
    omega
  · exact ⟨ft.2.1.trans fa.2.1,ft.2.2.2.1.trans fa.2.2.2.1,ft.2.2.2.2.1.trans fa.2.2.2.2.1,
      fun i _ _ _ _ _ _ _ _ _ hi hj _ _ _ => keep i hi hj,
      fun i _ h24 h25 h26 h27 _ _ => (ft.2.2.2.2.2.2 i h24 h25 h26 h27).trans (fa.2.2.2.2.2.2 i h24 h25 h26 h27)⟩

end Maxwell.Cost.CalibrationMatrix.Horner
