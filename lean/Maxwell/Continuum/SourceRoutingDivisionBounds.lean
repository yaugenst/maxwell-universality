import Maxwell.Continuum.SourceRoutingTreeDivision

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.Division
set_option maxRecDepth 16384
set_option maxHeartbeats 1800000

def result (v : ℕ→ℕ) (source divisor targetQ targetR : ℕ) : ℕ→ℕ :=
  Function.update (Function.update v targetQ (v source/v divisor)) targetR (v source%v divisor)

theorem result_width (v : ℕ→ℕ) (source divisor targetQ targetR B : ℕ) (hs : source∈ids)
    (hv : ∀i∈ids,(v i).bits.length ≤ B) : ∀i∈ids,(result v source divisor targetQ targetR i).bits.length ≤ B := by
  intro i hi
  by_cases hr : i=targetR
  · subst i
    simpa only [result,Function.update_self] using
      (Maxwell.Continuum.RationalWords.bits_mono (Nat.mod_le (v source) (v divisor))).trans (hv source hs)
  · by_cases hq : i=targetQ
    · subst i
      simpa only [result,Function.update_of_ne hr,Function.update_self] using
        (Maxwell.Continuum.RationalWords.bits_mono (Nat.div_le_self (v source) (v divisor))).trans (hv source hs)
    · simpa only [result,Function.update_of_ne hr,Function.update_of_ne hq] using hv i hi

theorem result_other (v : ℕ→ℕ) (source divisor targetQ targetR i : ℕ) (hq : i≠targetQ) (hr : i≠targetR) :
    result v source divisor targetQ targetR i=v i := by simp only [result,Function.update_of_ne hr,Function.update_of_ne hq]

theorem result_zero (v : ℕ→ℕ) (source divisor targetQ targetR : ℕ)
    (hq : targetQ∈controls) (hr : targetR∈controls)
    (hz : ∀i∈Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,v i=0) :
    ∀i∈Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,result v source divisor targetQ targetR i=0 := by
  intro i hi
  have different : i≠targetQ ∧ i≠targetR := by
    simp only [controls,Finset.mem_Icc] at hq hr
    simp only [Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,Finset.mem_insert,Finset.mem_singleton] at hi
    omega
  rw [result_other _ _ _ _ _ _ different.1 different.2]
  exact hz i hi

#print axioms result_width
end Maxwell.Cost.RoutingPorts.Complete.Tree.Division
