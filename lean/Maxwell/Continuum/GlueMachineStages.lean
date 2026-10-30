import Maxwell.Continuum.RationalTaylorProgram
import Maxwell.Continuum.RationalTaylorCenters
import Maxwell.Continuum.ProfileGlueEvaluation
import Maxwell.Continuum.NatAssignOutputWidth
import Maxwell.Cost.SelectedParameters.Compare

/-! Stored-word stages for the actual branch and reciprocal in profile glue evaluation. -/

namespace Maxwell.Continuum.GlueMachine
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

def extra : Finset ℕ := RationalTaylor.ids∪{608,609}
def ids : Finset ℕ := SelectedParameters.Compare.ids extra
def workspace : Finset ℕ := {0,1,2,3}∪ids

def initialValues (a b i : ℕ) : ℕ := if i=600 then a else if i=601 then b else 0
def initializedValues (a b N i : ℕ) : ℕ := if i=608 then 1 else if i=609 then N+1 else initialValues a b i
def comparedValues (a b N : ℕ) : ℕ→ℕ :=
  NatAssign.values (SelectedParameters.Compare.prepare 608 609 600 601) (initializedValues a b N)

def initializeStage : ℕ→List NatAssign.Instruction := fun N => [.literal 608 1,.literal 609 (N+1)]
def prepareExp : List NatAssign.Instruction := [.copy 600 606,.copy 601 600,.copy 606 601,.literal 606 0]
def writeZero : List NatAssign.Instruction := [.literal 602 0,.literal 603 0,.literal 604 1]
def preparedValues (a b N : ℕ) : ℕ→ℕ := NatAssign.values prepareExp (comparedValues a b N)
def order (N : ℕ) : ℕ := Calibration.taylorOrder (N+1) N-1
def seedWidth (N W : ℕ) : ℕ := W+N+4
def preparedWidth (N W : ℕ) : ℕ := 2^4*(seedWidth N W+1)
def stageCost (N W : ℕ) : ℕ := 2^50*(seedWidth N W+2)^2

theorem extra_ge (i : ℕ) (hi : i∈extra) : 40 ≤ i := by
  simp only [extra,RationalTaylor.ids,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hi
  omega

theorem ids_ge (i : ℕ) (hi : i∈ids) : 4 ≤ i := by
  simp only [ids,SelectedParameters.Compare.ids,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hi
  rcases hi with hi | hi
  · exact (by omega : 4 ≤ 40).trans (extra_ge i hi)
  · omega

theorem stages_valid (N : ℕ) : (∀ i∈initializeStage N, i.Valid ids) ∧
    (∀ i∈prepareExp, i.Valid ids) ∧ (∀ i∈writeZero, i.Valid ids) := by
  simp [initializeStage,prepareExp,writeZero,NatAssign.Instruction.Valid,ids,
    SelectedParameters.Compare.ids,extra,RationalTaylor.ids]

theorem initialize_values (a b N : ℕ) :
    NatAssign.values (initializeStage N) (initialValues a b)=initializedValues a b N := by
  ext i
  by_cases hi : i=608
  · subst i; simp [initializeStage,NatAssign.values,NatAssign.Instruction.update,
      NatAssign.Instruction.target,NatAssign.Instruction.value,initializedValues]
  by_cases hj : i=609
  · subst i; simp [initializeStage,NatAssign.values,NatAssign.Instruction.update,
      NatAssign.Instruction.target,NatAssign.Instruction.value,initializedValues]
  simp [initializeStage,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,
    NatAssign.Instruction.value,initializedValues,hi,hj]

theorem initial_width (a b N W : ℕ) (ha : a.bits.length≤W) (hb : b.bits.length≤W) (i : ℕ) :
    (initialValues a b i).bits.length≤seedWidth N W := by
  unfold initialValues seedWidth
  split_ifs <;> first | omega | simp

theorem initialized_width (a b N W : ℕ) (ha : a.bits.length≤W) (hb : b.bits.length≤W) (i : ℕ) :
    (initializedValues a b N i).bits.length≤seedWidth N W := by
  have h1 : (1:ℕ).bits.length=1 := by decide
  have hn := RationalTaylor.nat_bits_le_self (N+1)
  have hi := initial_width a b N W ha hb i
  unfold seedWidth at hi ⊢
  unfold initializedValues
  split_ifs <;> omega

theorem compared_inputs (a b N : ℕ) :
    comparedValues a b N 600=a ∧ comparedValues a b N 601=b := by
  simp [comparedValues,SelectedParameters.Compare.prepare,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,NatAssign.Instruction.value,initializedValues,initialValues]

theorem compared_width (a b N W : ℕ) (ha : a.bits.length≤W) (hb : b.bits.length≤W) (i : ℕ) :
    (comparedValues a b N i).bits.length≤seedWidth N W := by
  have he := SelectedParameters.Compare.prepared 608 609 600 601 (by decide) (by decide) (by decide) (by decide)
    (initializedValues a b N)
  have h30 := initialized_width a b N W ha hb 608
  have h31 := initialized_width a b N W ha hb 609
  have h32 := initialized_width a b N W ha hb 600
  have h33 := initialized_width a b N W ha hb 601
  have hi := initialized_width a b N W ha hb i
  unfold comparedValues
  rw [he]
  simp only [Function.update_apply]
  split_ifs <;> assumption

theorem prepared_inputs (a b N : ℕ) : preparedValues a b N 600=b ∧ preparedValues a b N 601=a := by
  simp [preparedValues,prepareExp,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,NatAssign.Instruction.value,(compared_inputs a b N).1,(compared_inputs a b N).2]

theorem prepared_width (a b N W : ℕ) (ha : a.bits.length≤W) (hb : b.bits.length≤W)
    (i : ℕ) (hi : i∈ids) : (preparedValues a b N i).bits.length≤preparedWidth N W := by
  have hh := NatAssign.values_width_bound ids prepareExp (stages_valid N).2.1 (comparedValues a b N)
    (seedWidth N W) (fun i _ => compared_width a b N W ha hb i)
    (by simp [prepareExp,NatAssign.Instruction.literalWidth]) i hi
  have hl : prepareExp.length=4 := rfl
  rw [hl] at hh
  exact (Nat.le_succ _).trans hh

theorem stage_executes (N W : ℕ) (ins : List NatAssign.Instruction)
    (hv : ∀ a∈ins, a.Valid ids) (hl : ins.length≤8)
    (hc : ∀ a∈ins, a.literalWidth≤seedWidth N W)
    (v : ℕ→ℕ) (hw : ∀ i∈ids, (v i).bits.length≤seedWidth N W)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : NatAssign.Bank ids v s.val) (hsc : NatAssign.Scratch s.val) :
    ∃ cost t, Executes input tape (NatAssign.code ins) cost s t ∧
      cost≤stageCost N W ∧ NatAssign.Bank ids (NatAssign.values ins v) t.val ∧
      NatAssign.Scratch t.val ∧ BinaryPrecision.Frame workspace s.val t.val := by
  obtain ⟨cost,t,he,hcost,hb,hsc',hframe⟩ := NatAssign.executes ids ids_ge ins hv v input tape s hs hsc
  have hp := NatAssign.price_bound ids ins hv v (seedWidth N W) hw hc
  have hcoef : 3000*8^ins.length≤(2:ℕ)^50 := by
    calc
      _ ≤ 3000*8^8 := Nat.mul_le_mul_left 3000 (Nat.pow_le_pow_right (by decide) hl)
      _ ≤ _ := by norm_num
  have hf : NatAssign.changes ins⊆workspace := by
    intro i hi
    simp only [NatAssign.changes,Finset.mem_union,List.mem_toFinset,List.mem_map] at hi
    rcases hi with hi | ⟨a,ha,rfl⟩
    · exact Finset.mem_union_left _ hi
    · apply Finset.mem_union_right
      have h := hv a ha
      cases a <;> first | exact h | exact h.2.1
  exact ⟨cost,t,he,hcost.trans (hp.trans (Nat.mul_le_mul_right _ hcoef)),hb,hsc',hframe.mono hf⟩

#print axioms prepared_inputs
#print axioms prepared_width
#print axioms stage_executes

end Maxwell.Continuum.GlueMachine
