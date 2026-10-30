import Maxwell.Continuum.SourceRoutingGeometryArithmetic

namespace Maxwell.Cost.RoutingPorts.Complete.GeometryArithmetic
open Maxwell.Continuum.RationalDataflow

def divided (v : ℕ→ℕ) (source divisor quotient remainder : ℕ) : ℕ→ℕ :=
  Function.update (Function.update v quotient (v source/v divisor)) remainder (v source%v divisor)

theorem divided_width (v : ℕ→ℕ) (source divisor quotient remainder B : ℕ)
    (hsource : source∈ids) (width : ∀i∈ids,(v i).bits.length ≤ B) :
    ∀i∈ids,(divided v source divisor quotient remainder i).bits.length ≤ B := by
  intro i hi
  by_cases hr : i=remainder
  · subst i
    simpa only [divided,Function.update_self] using
      (Maxwell.Continuum.RationalWords.bits_mono (Nat.mod_le (v source) (v divisor))).trans (width source hsource)
  · by_cases hq : i=quotient
    · subst i
      simpa only [divided,Function.update_of_ne hr,Function.update_self] using
        (Maxwell.Continuum.RationalWords.bits_mono (Nat.div_le_self (v source) (v divisor))).trans (width source hsource)
    · simpa only [divided,Function.update_of_ne hr,Function.update_of_ne hq] using width i hi

theorem divided_other (v : ℕ→ℕ) (source divisor quotient remainder i : ℕ)
    (hq : i≠quotient) (hr : i≠remainder) : divided v source divisor quotient remainder i=v i := by
  simp only [divided,Function.update_of_ne hr,Function.update_of_ne hq]

theorem divided_zero (v : ℕ→ℕ) (source divisor quotient remainder : ℕ)
    (hq : quotient∈controls) (hr : remainder∈controls)
    (zero : ∀i∈NaturalQuotient.workPorts,v i=0) :
    ∀i∈NaturalQuotient.workPorts,divided v source divisor quotient remainder i=0 := by
  intro i hi
  have different : i≠quotient ∧ i≠remainder := by
    simp only [controls,Finset.mem_Icc] at hq hr
    simp only [NaturalQuotient.workPorts,Finset.mem_insert,Finset.mem_singleton] at hi
    omega
  rw [divided_other _ _ _ _ _ _ different.1 different.2]
  exact zero i hi

end Maxwell.Cost.RoutingPorts.Complete.GeometryArithmetic
