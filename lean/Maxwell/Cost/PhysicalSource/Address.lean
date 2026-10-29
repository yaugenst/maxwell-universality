import Maxwell.Cost.Structured.NatAssign.Bounds
import Maxwell.Codec.EdgeIndex

/-! The source overlay's exact orientation-major edge address is computed
from stored dimensions, orientation offset, and retained coordinates. -/
namespace Maxwell.Cost.PhysicalSource.Address
open Structured RationalAccumulator
set_option maxHeartbeats 1000000

def ids : Finset ℕ := {333,370,371,372,373,374,375}
def instructions : List NatAssign.Instruction :=
  [.copy 373 333,.multiply 370 333,.add 374 333,.multiply 371 333,.add 375 333,.add 372 333]
def code : Code := NatAssign.code instructions

def result (v : ℕ → ℕ) : ℕ := ((v 373*v 370+v 374)*v 371+v 375)+v 372

theorem values_result (v : ℕ → ℕ) : NatAssign.values instructions v 333 = result v := by
  simp [instructions,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,
    NatAssign.Instruction.value,Function.update,result]
  ring

theorem valid : ∀ a ∈ instructions, a.Valid ids := by
  intro a ha
  simp [instructions] at ha
  rcases ha with rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num [NatAssign.Instruction.Valid,ids]

/-- Six actual word operations compute the address. All array descriptors,
source archives, dimension words, and coordinates are preserved. -/
theorem executes (v : ℕ → ℕ) (B : ℕ) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hb : NatAssign.Bank ids v s.val) (hr : NatAssign.Scratch s.val)
    (hB : ∀ i ∈ ids, (v i).bits.length≤B) :
    ∃ cost t, cost≤3000*8^6*(B+2)^2 ∧ Executes input tape code cost s t ∧
      Word t.val 333 (result v) ∧ NatAssign.Scratch t.val ∧
      BinaryPrecision.Frame {0,1,2,3,333} s.val t.val := by
  obtain ⟨c,t,he,hc,ht,hs,hf⟩ := NatAssign.executes ids
    (by intro i hi; simp only [ids,Finset.mem_insert,Finset.mem_singleton] at hi; omega)
    instructions valid v input tape s hb hr
  refine ⟨c,t,?_,he,?_,hs,?_⟩
  · have hl : ∀ a ∈ instructions, a.literalWidth≤B := by
      intro a ha
      simp [instructions] at ha
      rcases ha with rfl|rfl|rfl|rfl|rfl|rfl <;> exact Nat.zero_le _
    exact hc.trans (by simpa only [instructions,List.length_cons,List.length_nil] using
      NatAssign.price_bound ids instructions valid v B hB hl)
  · simpa only [values_result] using ht 333 (by decide)
  · simpa [NatAssign.changes,instructions,NatAssign.Instruction.target] using hf

theorem result_x {box : Target.Box} (v : ℕ→ℕ)
    (i : Fin box.nx) (j : Fin (box.ny-1)) (k : Fin (box.nz-1))
    (h : v 370=box.ny-1 ∧ v 371=box.nz-1 ∧ v 372=0 ∧
      v 373=i.val ∧ v 374=j.val ∧ v 375=k.val) :
    result v = Codec.edgeIndex (B:=box) (.inl (i,j,k)) := by
  simp [result,h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2]

theorem result_y {box : Target.Box} (v : ℕ→ℕ)
    (i : Fin (box.nx-1)) (j : Fin box.ny) (k : Fin (box.nz-1))
    (h : v 370=box.ny ∧ v 371=box.nz-1 ∧ v 372=box.nx*((box.ny-1)*(box.nz-1)) ∧
      v 373=i.val ∧ v 374=j.val ∧ v 375=k.val) :
    result v = Codec.edgeIndex (B:=box) (.inr (.inl (i,j,k))) := by
  simp only [result,h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2,
    Codec.edgeIndex_y]
  omega

theorem result_z {box : Target.Box} (v : ℕ→ℕ)
    (i : Fin (box.nx-1)) (j : Fin (box.ny-1)) (k : Fin box.nz)
    (h : v 370=box.ny-1 ∧ v 371=box.nz ∧
      v 372=box.nx*((box.ny-1)*(box.nz-1))+(box.nx-1)*(box.ny*(box.nz-1)) ∧
      v 373=i.val ∧ v 374=j.val ∧ v 375=k.val) :
    result v = Codec.edgeIndex (B:=box) (.inr (.inr (i,j,k))) := by
  simp only [result,h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2,
    Codec.edgeIndex_z]
  omega

end Maxwell.Cost.PhysicalSource.Address
