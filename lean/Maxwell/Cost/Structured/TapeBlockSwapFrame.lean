import Maxwell.Cost.Structured.TapeBlockSwap
import Maxwell.Cost.Structured.RenameFrame

/-! A symbolic bank bound suffices to protect caller tapes during a renamed
subroutine. No enumeration of the fixed arithmetic circuit is required. -/
namespace Maxwell.Cost.Structured.TapeBlockSwap

theorem outside_image {base count gap : ℕ} (separated : count≤gap)
    (used : Finset ℕ) (bound : ∀j∈used,j<base+gap) (i : ℕ)
    (lo : base≤ i) (hi : i<base+count) :
    i∉used.image (permutation base count gap separated) := by
  intro member
  obtain ⟨j,hj,eq⟩:=Finset.mem_image.mp member
  have inverted : j=permutation base count gap separated i := by
    calc
      j=permutation base count gap separated (permutation base count gap separated j) :=
        (involutive base count gap separated j).symm
      _=permutation base count gap separated i:=congrArg (permutation base count gap separated) eq
  rw [apply_inside base count gap separated i lo hi] at inverted
  have :=bound j hj
  omega

theorem retained {base count gap : ℕ} (separated : count≤gap)
    (used : Finset ℕ) (bound : ∀j∈used,j<base+gap) {s t : BitRAMState}
    (frame : BinaryPrecision.Frame (used.image (permutation base count gap separated)) s t)
    (i : ℕ) (lo : base≤ i) (hi : i<base+count) : t.tapes i=s.tapes i :=
  frame.tapes i (outside_image separated used bound i lo hi)

#print axioms outside_image
#print axioms retained
end Maxwell.Cost.Structured.TapeBlockSwap
