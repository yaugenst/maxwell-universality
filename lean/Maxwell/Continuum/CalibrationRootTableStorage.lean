import Maxwell.Continuum.CalibrationRootTableLoop
import Maxwell.Continuum.CalibrationRootGridCoefficientBounds
import Maxwell.Continuum.CalibrationNormalizationAllocation

/-! Concrete polynomial raw storage and a fixed runtime plan computing
the full coefficient count, slot width, and destination address. -/
namespace Maxwell.Continuum.RationalDataflow.RootTable
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 4500000
set_option maxRecDepth 8192

def storageWidth (grid N B I : ℕ) : ℕ := 2^256*(grid^3+1)*(N+B+I+20)^4

theorem storageWidth_pos (grid N B I : ℕ) : 0<storageWidth grid N B I := by
  unfold storageWidth
  positivity

theorem entryWidth_le_storageWidth (grid N B I : ℕ) :
    entryWidth grid N B I≤storageWidth grid N B I := by
  have hraw := RootGrid.coefficientRawWidth_polynomial grid N (RootIndexed.decodedWidth B) I
  have harg : N+RootIndexed.decodedWidth B+I+20≤2^16*(N+B+I+20) := by
    unfold RootIndexed.decodedWidth
    omega
  have hp : 2^185*(grid^3+1)*(N+RootIndexed.decodedWidth B+I+20)^4≤
      2^249*((grid^3+1)*(N+B+I+20)^4) := by
    calc
      _≤2^185*(grid^3+1)*(2^16*(N+B+I+20))^4 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left harg 4)
      _=_ := by ring
  have hraw' := hraw.trans hp
  have hone : 1≤(grid^3+1)*(N+B+I+20)^4 :=
    one_le_mul_of_one_le_of_one_le (by omega) (one_le_pow₀ (by omega))
  unfold entryWidth RootComponent.width storageWidth
  rw [mul_assoc]
  omega

def allocationIds : Finset ℕ := RootFrequency.ids∪{345,346,347,348,349,570,571,572,573,640}
def storagePlan : List NatAssign.Instruction :=
  [.copy 331 343,.multiply 331 343,.multiply 331 343,
   .copy 343 570,.literal 348 2,.multiply 348 570,.literal 348 1,.add 348 343,
   .copy 640 349,.add 345 349,.add 346 349,.literal 348 20,.add 348 349,
   .copy 349 348,.multiply 348 349,.copy 349 348,.multiply 348 349,
   .copy 349 571,.multiply 343 571,.literal 348 (2^256),.multiply 348 571,
   .copy 347 572,.literal 573 0,.literal 348 0,.literal 349 0]
def storageValues (v : ℕ→ℕ) := NatAssign.values storagePlan v

theorem storagePlan_valid : ∀a∈storagePlan,a.Valid allocationIds := by
  simp [storagePlan,NatAssign.Instruction.Valid,allocationIds,RootFrequency.ids]

theorem storagePlan_length : storagePlan.length=25 := rfl

theorem storageValues_outputs (v : ℕ→ℕ) :
    storageValues v 570=2*(v 331)^3 ∧
    storageValues v 571=storageWidth (v 331) (v 640) (v 345) (v 346) ∧
    storageValues v 572=v 347 ∧ storageValues v 573=0 ∧
    storageValues v 348=0 ∧ storageValues v 349=0 := by
  simp only [storageValues,storagePlan,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,NatAssign.Instruction.value,Function.update_self,
    Function.update_of_ne (by decide : (570:ℕ)≠349),Function.update_of_ne (by decide : (570:ℕ)≠348)]
  simp [storageWidth]
  constructor <;> ring

theorem storageValues_keep (v : ℕ→ℕ) (i : ℕ)
    (hi : i≠343 ∧ i≠348 ∧ i≠349 ∧ i≠570 ∧ i≠571 ∧ i≠572 ∧ i≠573) : storageValues v i=v i := by
  exact values_unchanged storagePlan v i (by
    simp only [storagePlan,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,
      NatAssign.Instruction.target]
    rcases hi with ⟨h0,h1,h2,h3,h4,h5,h6⟩
    omega)

theorem storagePlan_literals (C : ℕ) (hC : 257≤C) : ∀a∈storagePlan,a.literalWidth≤C := by
  have hp : (2^256:ℕ).bits.length=257 := by decide
  simp only [storagePlan,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,
    NatAssign.Instruction.literalWidth,hp,show (0:ℕ).bits.length=0 by rfl,
    show (1:ℕ).bits.length=1 by rfl,show (20:ℕ).bits.length=5 by rfl,
    show (2:ℕ).bits.length=2 by rfl]
  omega

theorem storage_executes (v : ℕ→ℕ) (C : ℕ) (hC : 257≤C)
    (hw : ∀i∈allocationIds,(v i).bits.length≤C)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hb : NatAssign.Bank allocationIds v s.val) (hz : NatAssign.Scratch s.val) :
    ∃cost t,Executes input tape (NatAssign.code storagePlan) cost s t ∧ cost≤stageCost C ∧
      NatAssign.Bank allocationIds (storageValues v) t.val ∧ NatAssign.Scratch t.val ∧
      BinaryPrecision.Frame (NatAssign.changes storagePlan) s.val t.val := by
  have hid (i : ℕ) (hi : i∈allocationIds) : 4 ≤ i := by
    rcases Finset.mem_union.mp hi with hi|hi
    · have hh := RootFrequency.ids_bounds i hi;omega
    · simp only [Finset.mem_insert,Finset.mem_singleton] at hi;omega
  obtain ⟨c,t,e,hc,b,z,f⟩ := NatAssign.executes allocationIds hid storagePlan storagePlan_valid v
    input tape s hb hz
  have hp := NatAssign.price_bound allocationIds storagePlan storagePlan_valid v C hw (storagePlan_literals C hC)
  have hcst : 3000*8^storagePlan.length≤(2:ℕ)^96 := by rw [storagePlan_length];norm_num
  exact ⟨c,t,e,hc.trans (hp.trans (Nat.mul_le_mul_right _ hcst)),b,z,f⟩

#print axioms entryWidth_le_storageWidth
#print axioms storage_executes
end Maxwell.Continuum.RationalDataflow.RootTable
