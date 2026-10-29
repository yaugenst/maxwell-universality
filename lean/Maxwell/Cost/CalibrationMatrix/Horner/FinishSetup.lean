import Maxwell.Cost.CalibrationMatrix.Horner.Correctness
import Maxwell.Cost.CalibrationMatrix.Scale.Semantics

namespace Maxwell.Cost.CalibrationMatrix.Horner
open Structured
set_option maxHeartbeats 1200000

def finishPort (i : Fin 4) : Fin 12 := if h : i.val < 2 then ⟨10+i.val,by omega⟩ else ⟨4+i.val,by omega⟩

theorem finishPort_injective : Function.Injective finishPort := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp [finishPort] at *

def Data.finishData {n : ℕ} (d : Data n) : Scale.Data n where
  width := d.width
  clock := d.clock
  bases := fun i => d.bases (finishPort i)
  K := d.S
  width_nonempty := d.width_nonempty
  width_positive := d.width_positive
  clock_length := d.clock_length
  separated := fun _i _j h => d.separated _ _ (fun he => h (finishPort_injective he))

def finishWords {n : ℕ} (words : Fin 12 → Vector (List Bool) n) : Fin 4 → Vector (List Bool) n :=
  fun i => words (finishPort i)

def FinishFrame (s t : BitRAMState) : Prop :=
  t.inputHead = s.inputHead ∧ t.randomCursor = s.randomCursor ∧ t.output = s.output ∧
  (∀ i, (i = 4 ∨ 10 ≤ i) → (i < 30 ∨ 36 < i) → i ∉ mutableTapes → i ≠ 126 → t.tapes i = s.tapes i) ∧
  (∀ i, 15 ≤ i → i ≠ 24 → i ≠ 25 → i ≠ 26 → i ≠ 27 → i ≠ 28 → i ≠ 29 → t.registers i = s.registers i)

theorem FinishFrame.trans {s t u : BitRAMState} (h : FinishFrame s t) (k : FinishFrame t u) : FinishFrame s u :=
  ⟨k.1.trans h.1,k.2.1.trans h.2.1,k.2.2.1.trans h.2.2.1,
    fun i hi hj hk hl => (k.2.2.2.1 i hi hj hk hl).trans (h.2.2.2.1 i hi hj hk hl),
    fun i hi a b c d e f => (k.2.2.2.2 i hi a b c d e f).trans (h.2.2.2.2 i hi a b c d e f)⟩

theorem FinishFrame.of_horner {s t : BitRAMState} (h : Frame s t) : FinishFrame s t :=
  ⟨h.1,h.2.1,h.2.2.1,fun i hi hj hk _ => h.2.2.2.1 i hi hj hk,h.2.2.2.2⟩

theorem FinishFrame.of_assignment {target : ℕ} {s t : BitRAMState}
    (ht : target ∈ mutableTapes ∨ target = 126) (h : WordTransfer.Frame target target s t) : FinishFrame s t := by
  refine ⟨h.2.1,h.2.2.2.1,h.2.2.2.2.1,?_,fun i _ a b c d _ _ => h.2.2.2.2.2.2 i a b c d⟩
  intro i _ _ hi hj
  have he : i ≠ target := by
    intro he
    rcases ht with ht | ht
    · exact hi (he ▸ ht)
    · exact hj (he.trans ht)
  exact h.2.2.2.2.2.1 i he he

theorem Data.finish_sized {n B : ℕ} {d : Data n} (h : d.Sized B) : d.finishData.Sized B :=
  ⟨h.1,h.2.1,fun i => h.2.2.2.2.1 (finishPort i),h.2.2.2.2.2.2⟩

def finishSetupCode : Code := .seq (Assign.code 130 120) (.seq (Assign.code 131 121) (Assign.code 127 126))

/-- Copy actual product and scalar descriptors into the finite scaling pass.
All overwritten descriptor cleanup is charged. -/
theorem finish_setup {n : ℕ} (d : Data n) (words : Fin 12 → Vector (List Bool) n)
    (B : ℕ) (hsized : d.Sized B) (input : List Bool) (tape : ℕ → Bool)
    (count : List Bool) (s : Store) (hw : WorkReady count B s.val) (hd : Stored d words s.val) :
    ∃ t, Executes input tape finishSetupCode
      (6*(d.bases 0).length+4+(15*(d.bases 10).length+17)+
        (6*(d.bases 1).length+4+(15*(d.bases 11).length+17)+
          (6*d.K.bits.length+4+(15*d.S.bits.length+17)))) s t ∧
      WorkReady count B t.val ∧ Scale.Stored d.finishData (finishWords words) t.val ∧
      t.val.tapes 140 = s.val.tapes 140 ∧ t.val.memory = s.val.memory ∧
      (∀ i, i ≠ 120 → i ≠ 121 → i ≠ 126 → t.val.tapes i = s.val.tapes i) ∧ FinishFrame s.val t.val ∧
      6*(d.bases 0).length+4+(15*(d.bases 10).length+17)+
        (6*(d.bases 1).length+4+(15*(d.bases 11).length+17)+
          (6*d.K.bits.length+4+(15*d.S.bits.length+17))) ≤ 63*B+63 := by
  obtain ⟨a,ea,ha,ka,fa⟩ := Assign.executes 130 120 (by omega) input tape (d.bases 10) (d.bases 0) s
    (hd.bases 10) (hd.bases 0)
  obtain ⟨b,eb,hb,kb,fb⟩ := Assign.executes 131 121 (by omega) input tape (d.bases 11) (d.bases 1) a
    (BankArray.word_of_eq (ka 131 (by omega)) (hd.bases 11))
    (BankArray.word_of_eq (ka 121 (by omega)) (hd.bases 1))
  obtain ⟨t,et,ht,kt,ft⟩ := Assign.executes 127 126 (by omega) input tape d.S.bits d.K.bits b
    (BankArray.word_of_eq ((kb 127 (by omega)).trans (ka 127 (by omega))) hd.S)
    (BankArray.word_of_eq ((kb 126 (by omega)).trans (ka 126 (by omega))) hd.K)
  have keep (i : ℕ) (h120 : i ≠ 120) (h121 : i ≠ 121) (h126 : i ≠ 126) : t.val.tapes i = s.val.tapes i :=
    (kt i h126).trans ((kb i h121).trans (ka i h120))
  have hm : t.val.memory = s.val.memory := ft.2.2.1.trans (fb.2.2.1.trans fa.2.2.1)
  refine ⟨t,ea.seq (eb.seq et),hw.of_tapes (fun i hi => keep i (by dsimp [WorkTape] at hi;omega)
    (by dsimp [WorkTape] at hi;omega) (by dsimp [WorkTape] at hi;omega)),
    ⟨BankArray.word_of_eq (keep 100 (by omega) (by omega) (by omega)) hd.width,
      BankArray.word_of_eq (keep 101 (by omega) (by omega) (by omega)) hd.clock,?_,ht,
      fun i => by simpa only [hm,Data.finishData,finishWords] using hd.arrays (finishPort i)⟩,
    keep 140 (by omega) (by omega) (by omega),hm,keep,
    ((FinishFrame.of_assignment (by simp [mutableTapes]) fa).trans
      (FinishFrame.of_assignment (by simp [mutableTapes]) fb)).trans
      (FinishFrame.of_assignment (Or.inr rfl) ft),?_⟩
  · intro i
    fin_cases i
    · exact BankArray.word_of_eq ((kt 120 (by omega)).trans (kb 120 (by omega))) ha
    · exact BankArray.word_of_eq (kt 121 (by omega)) hb
    · exact BankArray.word_of_eq (keep 128 (by omega) (by omega) (by omega)) (hd.bases 6)
    · exact BankArray.word_of_eq (keep 129 (by omega) (by omega) (by omega)) (hd.bases 7)
  · have h0 := hsized.2.2.2.2.1 0
    have h1 := hsized.2.2.2.2.1 1
    have h10 := hsized.2.2.2.2.1 10
    have h11 := hsized.2.2.2.2.1 11
    have hk := hsized.2.2.2.2.2.1
    have hs := hsized.2.2.2.2.2.2
    omega

end Maxwell.Cost.CalibrationMatrix.Horner
