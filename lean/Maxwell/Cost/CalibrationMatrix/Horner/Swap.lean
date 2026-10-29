import Maxwell.Cost.CalibrationMatrix.Horner.Select
import Maxwell.Cost.CalibrationMatrix.Horner.Frame

namespace Maxwell.Cost.CalibrationMatrix.Horner
open Structured
set_option maxHeartbeats 1000000

theorem baseBank_injective : Function.Injective baseBank := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [baseBank]

theorem baseBank_ne_scalar (i : Fin 12) : baseBank i ≠ 126 ∧ baseBank i ≠ 127 := by
  unfold baseBank
  split_ifs <;> omega

def swapCode (p q : Fin 12) : Code := WordSwap.code (baseBank p) (baseBank q) 109

theorem swap {n : ℕ} (d : Data n) (words : Fin 12 → Vector (List Bool) n)
    (p q : Fin 12) (hpq : p ≠ q) (hp : baseBank p ∈ mutableTapes) (hq : baseBank q ∈ mutableTapes)
    (B : ℕ) (hsized : d.Sized B) (input : List Bool) (tape : ℕ → Bool) (count : List Bool)
    (s : Store) (hw : WorkReady count B s.val) (hd : Stored d words s.val) :
    ∃ cost, ∃ t : Store, cost ≤ 36*B+33 ∧ Executes input tape (swapCode p q) cost s t ∧
      WorkReady count B t.val ∧ Stored (d.permute (Equiv.swap p q)) (fun i => words (Equiv.swap p q i)) t.val ∧
      (∀ i, i = 112 ∨ i = 113 ∨ i = 114 ∨ i = 115 ∨ i = 140 → t.val.tapes i = s.val.tapes i) ∧
      t.val.memory = s.val.memory ∧ Frame s.val t.val := by
  obtain ⟨vi,hvi,hvl,hr,hi,h104,h107,h106,h37,h108,h109⟩ := hw
  have hpbound := baseBank_bounds p
  have hqbound := baseBank_bounds q
  obtain ⟨t,he,htp,htq,ht109,htf⟩ := WordSwap.executes (baseBank p) (baseBank q) 109
    (fun he => hpq (baseBank_injective he)) (by omega) (by omega)
    input tape (d.bases p) (d.bases q) s (hd.bases p) (hd.bases q) h109
  have keep (i : ℕ) (hip : i ≠ baseBank p) (hiq : i ≠ baseBank q) (hi109 : i ≠ 109) :
      t.val.tapes i = s.val.tapes i := htf.2.2.2.2.2.1 i hip hiq hi109
  have low (i : ℕ) (hilow : i < 120) (hi109 : i ≠ 109) : t.val.tapes i = s.val.tapes i :=
    keep i (by omega) (by omega) hi109
  refine ⟨12*(2*(d.bases p).length+(d.bases q).length)+33,t,?_,he,
    ⟨vi,hvi,hvl,hr.of_tapes (fun i hi => low i (by omega) (by omega)),
      ⟨BankArray.word_of_eq (low 102 (by omega) (by omega)) hi.1,
        BankArray.word_of_eq (low 103 (by omega) (by omega)) hi.2⟩,
      BankArray.word_of_eq (low 104 (by omega) (by omega)) h104,
      BankArray.word_of_eq (low 107 (by omega) (by omega)) h107,
      RationalAccumulator.blank_of_eq (low 106 (by omega) (by omega)) h106,
      RationalAccumulator.blank_of_eq (low 37 (by omega) (by omega)) h37,
      RationalAccumulator.blank_of_eq (low 108 (by omega) (by omega)) h108,ht109⟩,
    ?_,fun i hi => keep i (by omega) (by omega) (by omega),htf.2.2.1,
    Frame.of_swap hp hq (by simp [mutableTapes]) htf⟩
  · have hpl := hsized.2.2.2.2.1 p
    have hql := hsized.2.2.2.2.1 q
    omega
  · refine ⟨BankArray.word_of_eq (low 100 (by omega) (by omega)) hd.width,
      BankArray.word_of_eq (low 101 (by omega) (by omega)) hd.clock,
      BankArray.word_of_eq (low 110 (by omega) (by omega)) hd.matrixPositiveBase,
      BankArray.word_of_eq (low 111 (by omega) (by omega)) hd.matrixNegativeBase,?_,
      RationalAccumulator.word_of_eq (keep 126 (baseBank_ne_scalar p).1.symm (baseBank_ne_scalar q).1.symm (by omega)) hd.K,
      RationalAccumulator.word_of_eq (keep 127 (baseBank_ne_scalar p).2.symm (baseBank_ne_scalar q).2.symm (by omega)) hd.S,
      by simpa only [Data.permute,htf.2.2.1] using hd.matrixPositive,
      by simpa only [Data.permute,htf.2.2.1] using hd.matrixNegative,
      fun i => by simpa only [Data.permute,htf.2.2.1] using hd.arrays (Equiv.swap p q i)⟩
    intro i
    by_cases hip : i = p
    · subst i;simpa [Data.permute] using htp
    · by_cases hiq : i = q
      · subst i;simpa [Data.permute] using htq
      · have hib := baseBank_bounds i
        simpa only [Data.permute,Equiv.swap_apply_of_ne_of_ne hip hiq] using
          BankArray.word_of_eq (keep _ (fun he => hip (baseBank_injective he))
            (fun he => hiq (baseBank_injective he)) (by omega)) (hd.bases i)

end Maxwell.Cost.CalibrationMatrix.Horner
