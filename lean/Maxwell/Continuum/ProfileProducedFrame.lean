import Maxwell.Continuum.ProfileRoundedSpare
import Maxwell.Continuum.RationalDataflowTableHeaderSwap
import Maxwell.Continuum.RationalDataflowRowPlan

/-! The stored producer state is sufficient for the shared arithmetic
passes: its clean division bank and literal fixed-width rows are proved. -/
namespace Maxwell.Continuum.Profile.Runtime
open RationalDataflow Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 2500000
set_option maxRecDepth 16384

theorem clean_shared_ready {S : Finset ℕ} {v : ℕ→Parts} {s : Store}
    (hr : Ready S v s) (hz : DyadicFloor.Clean s.val) : SharedConversion.Ready S v s := by
  constructor
  · intro i hi
    rcases Finset.mem_union.mp hi with hi|hi
    · exact hr.1 i hi
    · rw [SharedConversion.work_values_zero v i hi]
      exact (zero_word_iff_blank _ _).mpr (hz.2 i (Finset.mem_union_right _ hi))
  · intro i hi
    by_cases h : i<4
    · exact hr.2 i h
    · have : i=4 := by omega
      subst i
      exact hz.1

theorem sharedReady_headerSwap {S : Finset ℕ} {v : ℕ→Parts} {s t : Store}
    (h : SharedConversion.Ready S v s)
    (f : BinaryPrecision.Frame (insert 216 PartArray.headerSlots) s.val t.val) :
    SharedConversion.Ready S v t := by
  constructor
  · intro i hi
    rcases Finset.mem_union.mp hi with hi|hi
    · exact (PartArray.Ready.headerSwap_frame h.rational f).1 i hi
    · exact word_of_eq (f.tapes i (by
        intro hm
        have bounds := PartArray.headerSlots_small i hm
        simp only [NaturalQuotient.workPorts,Finset.mem_insert,Finset.mem_singleton] at hi
        omega)) (h.1 i (Finset.mem_union_right _ hi))
  · intro i hi
    exact blank_of_eq (f.tapes i (by
      intro hm
      have := PartArray.headerSlots_small i hm
      omega)) (h.2 i hi)

theorem tableSeparatedFrom_symm {n m : ℕ} {a : PartArray.Table n} {b : PartArray.Table m}
    (h : a.SeparatedFrom b) : b.SeparatedFrom a := by
  intro x hx y hy
  exact (h y hy x hx).symm

#print axioms clean_shared_ready
end Maxwell.Continuum.Profile.Runtime
