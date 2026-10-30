import Maxwell.Continuum.GlueMachineProgram

/-! Fixed instructions compute the glue threshold and Taylor order from a
stored requested precision. No precision-dependent literal or unrolled
instruction list occurs in this setup. -/
namespace Maxwell.Continuum.GlueMachine.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

def ids : Finset ℕ := GlueMachine.ids∪{607,640,641,642,643}
def workspace : Finset ℕ := {0,1,2,3}∪ids

def initialValues (a b N i : ℕ) : ℕ :=
  if i=640 then N else GlueMachine.initialValues a b i

def setup : List NatAssign.Instruction :=
  [.literal 608 1,.copy 640 609,.add 608 609,
   .copy 609 641,.multiply 609 641,.literal 642 8,.multiply 642 641,
   .copy 640 643,.literal 642 2,.multiply 642 643,.add 643 641,
   .literal 642 7,.add 642 641,.literal 642 0,.literal 643 0]

def setupValues (a b N : ℕ) : ℕ→ℕ := NatAssign.values setup (initialValues a b N)

theorem order_eq (N : ℕ) : GlueMachine.order N=8*(N+1)^2+2*N+7 := by
  unfold GlueMachine.order Calibration.taylorOrder Calibration.taylorHalfOrder
  omega

theorem ids_ge (i : ℕ) (hi : i∈ids) : 4 ≤ i := by
  rcases Finset.mem_union.mp hi with hi | hi
  · exact GlueMachine.ids_ge i hi
  · simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    omega

theorem setup_valid : ∀i∈setup,i.Valid ids := by
  simp [setup,NatAssign.Instruction.Valid,ids,GlueMachine.ids,
    SelectedParameters.Compare.ids,GlueMachine.extra,RationalTaylor.ids]

theorem setupValues_order (a b N : ℕ) : setupValues a b N 641=GlueMachine.order N := by
  simp [setupValues,setup,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,NatAssign.Instruction.value,initialValues,order_eq]
  ring

theorem setupValues_precision (a b N : ℕ) : setupValues a b N 640=N := by
  simp [setupValues,setup,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,NatAssign.Instruction.value,initialValues]

theorem setupValues_aux (a b N : ℕ) : setupValues a b N 642=0 ∧ setupValues a b N 643=0 := by
  simp [setupValues,setup,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,NatAssign.Instruction.value]

theorem setupValues_core (a b N i : ℕ) (hi : i∈GlueMachine.ids) :
    setupValues a b N i=GlueMachine.initializedValues a b N i := by
  have hi640 : i≠640 := by
    intro he;subst i;contradiction
  have hi641 : i≠641 := by
    intro he;subst i;contradiction
  have hi642 : i≠642 := by
    intro he;subst i;contradiction
  have hi643 : i≠643 := by
    intro he;subst i;contradiction
  simp [setupValues,setup,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,NatAssign.Instruction.value,Function.update_apply,
    hi641,hi642,hi643,initialValues,hi640,GlueMachine.initializedValues]
  split_ifs <;> first | rfl | omega

theorem setup_literals (W : ℕ) (hW : 4≤W) : ∀i∈setup,i.literalWidth≤W := by
  simp [setup,NatAssign.Instruction.literalWidth,show (8:ℕ).bits.length=4 from rfl,
    show (2:ℕ).bits.length=2 from rfl,show (7:ℕ).bits.length=3 from rfl]
  omega

theorem initialValues_width (a b N W : ℕ) (ha : a.bits.length≤W) (hb : b.bits.length≤W)
    (hN : N.bits.length≤W) (i : ℕ) : (initialValues a b N i).bits.length≤W := by
  simp only [initialValues,GlueMachine.initialValues]
  split_ifs <;> first | assumption | simp

theorem setup_width (a b N W : ℕ) (ha : a.bits.length≤W) (hb : b.bits.length≤W)
    (hN : N.bits.length≤W) (hW : 4≤W) (i : ℕ) (hi : i∈ids) :
    (setupValues a b N i).bits.length≤2^15*(W+1) := by
  have hw := NatAssign.values_width_bound ids setup setup_valid (initialValues a b N) W
    (fun i _ => initialValues_width a b N W ha hb hN i)
    (setup_literals W hW) i hi
  exact (Nat.le_succ _).trans hw

theorem setup_executes (a b N W : ℕ) (ha : a.bits.length≤W) (hb : b.bits.length≤W)
    (hN : N.bits.length≤W) (hW : 4≤W)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : NatAssign.Bank ids (initialValues a b N) s.val) (hz : NatAssign.Scratch s.val) :
    ∃ cost t,Executes input tape (NatAssign.code setup) cost s t ∧
      cost≤2^60*(W+2)^2 ∧ NatAssign.Bank ids (setupValues a b N) t.val ∧
      NatAssign.Scratch t.val ∧ BinaryPrecision.Frame workspace s.val t.val ∧
      Word t.val 640 N ∧ Word t.val 641 (GlueMachine.order N) := by
  obtain ⟨cost,t,ex,hcost,bt,zt,ft⟩ := NatAssign.executes ids ids_ge setup setup_valid
    (initialValues a b N) input tape s hs hz
  have hp := NatAssign.price_bound ids setup setup_valid (initialValues a b N) W
    (fun i _ => initialValues_width a b N W ha hb hN i)
    (setup_literals W hW)
  have hc : cost≤2^60*(W+2)^2 := by
    apply hcost.trans (hp.trans _)
    apply Nat.mul_le_mul_right
    norm_num [setup]
  have hf : NatAssign.changes setup⊆workspace := by
    intro i hi
    simp only [NatAssign.changes,Finset.mem_union,List.mem_toFinset,List.mem_map] at hi
    rcases hi with hi | ⟨ins,hins,rfl⟩
    · exact Finset.mem_union_left _ hi
    · apply Finset.mem_union_right
      have h := setup_valid ins hins
      cases ins <;> first | exact h | exact h.2.1
  exact ⟨cost,t,ex,hc,bt,zt,ft.mono hf,
    by
      have h : Word t.val 640 (setupValues a b N 640) := bt 640 (by decide)
      simpa only [setupValues_precision] using h,
    by
      have h : Word t.val 641 (setupValues a b N 641) := bt 641 (by decide)
      simpa only [setupValues_order] using h⟩

#print axioms setup_executes
#print axioms setupValues_order
end Maxwell.Continuum.GlueMachine.Runtime
