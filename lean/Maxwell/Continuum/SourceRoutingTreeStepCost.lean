import Maxwell.Continuum.SourceRoutingTreeStep
import Maxwell.Continuum.SourceRoutingNodeCost

/-! The complete fixed loop body, including descriptor arithmetic and
the node-index increment, costs linear token work times cubic word width. -/

namespace Maxwell.Cost.RoutingPorts.Complete.Tree.Step
open Structured
set_option maxRecDepth 16384
set_option maxHeartbeats 1800000
set_option exponentiation.threshold 512

theorem cost_bound (v : ℕ→ℕ) (k B : ℕ) (hB : 3 ≤ B) (hn : v 811=2*2^k) (hw : v 812=k+2)
    (hwords : ∀i∈Division.ids,(v i).bits.length ≤ B) :
    cost v k B ≤ 2^300*(v 811+1)*(B+2)^3 := by
  have subset : NodeSetup.controls⊆Division.ids := by decide
  have width := descriptor_width v B hB hwords
  have hv := NodeWords.visit_bound (Descriptor.output v) k (wordBound B)
    ((Descriptor.output_count v).trans hn) ((Descriptor.output_width v).trans hw)
    (fun i hi => width i (subset hi))
  rw [Descriptor.output_count] at hv
  have hword : wordBound B+2 ≤ 2^28*(B+2) := by dsimp only [wordBound];omega
  have hcube := Nat.pow_le_pow_left hword 3
  have hsquare := Nat.pow_le_pow_left hword 2
  have node : NodeVisit.bound (Descriptor.output v) k (wordBound B)+1 ≤
      2^264*(v 811+1)*(B+2)^3 := by
    calc
      _ ≤ 2^180*(v 811+1)*(2^28*(B+2))^3 := hv.trans (Nat.mul_le_mul_left _ hcube)
      _ = _ := by ring
  have incrementCost : 3000*8^2*(wordBound B+2)^2 ≤ 2^80*(B+2)^2 := by
    calc
      _ ≤ 3000*8^2*(2^28*(B+2))^2 := Nat.mul_le_mul_left _ hsquare
      _ = (3000*8^2*(2^28)^2)*(B+2)^2 := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (by norm_num)
  have small : (B+2)^2 ≤ (v 811+1)*(B+2)^3 := by
    calc
      _ ≤ (B+2)^3 := by nlinarith
      _ ≤ _ := Nat.le_mul_of_pos_left _ (by omega)
  calc
    cost v k B ≤ (2^160+2^264+2^80)*((v 811+1)*(B+2)^3) := by
      dsimp only [cost]
      nlinarith only [node,incrementCost,small]
    _ ≤ _ := by
      rw [mul_assoc (2^300)]
      exact Nat.mul_le_mul_right _ (by norm_num)

#print axioms cost_bound
end Maxwell.Cost.RoutingPorts.Complete.Tree.Step
