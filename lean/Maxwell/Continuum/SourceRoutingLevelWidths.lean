import Maxwell.Continuum.SourceRoutingLevelValues

/-! Uniform width over an entire routing level follows from the closed
controller formulas, rather than repeated amplification of a width estimate. -/

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.Level
open Structured
set_option maxRecDepth 16384
set_option maxHeartbeats 1800000

def uniformWidth (L : ℕ) : ℕ := 2^30*(L+2)

theorem output_width (v : ℕ→ℕ) (B : ℕ) (hB : 3 ≤ B)
    (hw : ∀j∈Division.ids,(v j).bits.length ≤ B) :
    ∀j∈Division.ids,(Step.output v j).bits.length ≤ 4*(Step.wordBound B+1) := by
  have hv : ∀a∈Step.increment,a.Valid Division.ids := by
    simp [Step.increment,NatAssign.Instruction.Valid,Division.ids,Division.controls]
  have hl : ∀a∈Step.increment,a.literalWidth ≤ Step.wordBound B := by
    simp [Step.increment,NatAssign.Instruction.literalWidth,Step.wordBound]
    omega
  intro j hj
  have h := NatAssign.values_width_bound Division.ids Step.increment hv (Descriptor.output v)
    (Step.wordBound B) (Step.descriptor_width v B hB hw) hl j hj
  change (Step.output v j).bits.length+1 ≤ 4*(Step.wordBound B+1) at h
  omega

theorem basis_width (v : ℕ→ℕ) (i L : ℕ)
    (hw : ∀j∈Division.ids,(v j).bits.length ≤ L) (hi : i.bits.length ≤ L) :
    ∀j∈Division.ids,(basis v i j).bits.length ≤ 2*L+1 := by
  intro j hj
  by_cases he : j=815
  · subst j
    simp only [basis,Function.update_self]
    have h0:=hw 815 (by decide)
    have h1:=RationalAccumulator.bits_add_le (v 815) i
    omega
  · simp only [basis,Function.update_of_ne he]
    exact (hw j hj).trans (by omega)

theorem values_width (v : ℕ→ℕ) (i L : ℕ) (hL : 1 ≤ L)
    (hw : ∀j∈Division.ids,(v j).bits.length ≤ L) (hi : i.bits.length ≤ L) :
    ∀j∈Division.ids,(values v i j).bits.length ≤ uniformWidth L := by
  cases i with
  | zero =>
      intro j hj
      exact (hw j hj).trans (by dsimp only [uniformWidth];omega)
  | succ i =>
      rw [values_successor]
      have hi' : i.bits.length ≤ L :=
        (Maxwell.Continuum.RationalWords.bits_mono (Nat.le_succ i)).trans hi
      intro j hj
      have hh:=output_width (basis v i) (2*L+1) (by omega) (basis_width v i L hw hi') j hj
      exact hh.trans (by dsimp only [uniformWidth,Step.wordBound];omega)

#print axioms values_width
end Maxwell.Cost.RoutingPorts.Complete.Tree.Level
