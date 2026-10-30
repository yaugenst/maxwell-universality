import Maxwell.Continuum.RuntimeCounterClear

/-! A literal tape list is cleared by actual word scans. Noncanonical
countdowns and one-bit clocks are covered by their measured word lengths. -/

namespace Maxwell.Cost.Structured.WordCleanup
open RationalAccumulator (Blank)
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000

def code : List ℕ→Code
  | [] => .skip
  | i::rest => .seq (.call (TapeOps.clear i)) (code rest)

def Bounded (ids : List ℕ) (B : ℕ) (s : BitRAMState) : Prop :=
  ∀i∈ids,∃bits : List Bool,bits.length≤B ∧ BankArray.Word s i bits

def wordBudget (entries : List (ℕ×List Bool)) : ℕ := (entries.map (fun a => a.2.length)).sum

theorem bounded_entries (entries : List (ℕ×List Bool)) (s : BitRAMState)
    (hs : ∀a∈entries,BankArray.Word s a.1 a.2) :
    Bounded (entries.map Prod.fst) (wordBudget entries) s := by
  intro i hi
  obtain ⟨a,ha,he⟩ := List.mem_map.mp hi
  rw [←he]
  exact ⟨a.2,List.le_sum_of_mem (List.mem_map.mpr ⟨a,ha,rfl⟩),hs a ha⟩

theorem executes (ids : List ℕ) (B : ℕ) (input : List Bool) (tape : ℕ→Bool)
    (s : Store) (hs : Bounded ids B s.val) :
    ∃steps t, Executes input tape (code ids) steps s t ∧ steps ≤ ids.length*(6*B+4)+1 ∧
      (∀i∈ids,Blank t.val i) ∧ BinaryPrecision.Frame ids.toFinset s.val t.val := by
  induction ids generalizing s with
  | nil => exact ⟨1,s,Executes.skip s,by simp,by simp,BinaryPrecision.Frame.refl _ _⟩
  | cons i rest ih =>
    obtain ⟨bits,hlen,origin,hw⟩ := hs i (by simp)
    obtain ⟨a,ea,za,fa⟩ := RuntimeCounter.clear_executes i input tape bits origin s hw
    have ba : Bounded rest B a.val := by
      intro j hj
      by_cases hji : j=i
      · subst j
        refine ⟨[],Nat.zero_le _,?_⟩
        exact (RationalAccumulator.zero_word_iff_blank _ _).mpr za
      · obtain ⟨xs,hxs,hword⟩ := hs j (List.mem_cons_of_mem _ hj)
        exact ⟨xs,hxs,BankArray.word_of_eq (fa.tapes j (by simpa using hji)) hword⟩
    obtain ⟨cr,t,er,hcr,zt,fr⟩ := ih a ba
    refine ⟨6*bits.length+4+cr,t,ea.seq er,?_,?_,
      (fa.mono (by simp)).trans (fr.mono (by simp))⟩
    · simp only [List.length_cons]
      nlinarith only [hlen,hcr]
    · intro j hj
      rcases List.mem_cons.mp hj with hji|hj
      · subst j
        by_cases hi : i∈rest
        · exact zt i hi
        · exact RationalAccumulator.blank_of_eq (fr.tapes i (by simpa using hi)) za
      · exact zt j hj

#print axioms executes
#print axioms bounded_entries

end Maxwell.Cost.Structured.WordCleanup
