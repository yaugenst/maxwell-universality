import Maxwell.Continuum.RationalDataflowExpression

/-! Compiled expressions need only their actual input registers and their
temporary range. Unused lower-numbered registers are not part of the contract. -/
namespace Maxwell.Continuum.RationalDataflow.PolynomialExpression
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 3000000

def inputs : PolynomialExpression→Finset ℕ
  | .literal _ => ∅
  | .inputRegister i => {i}
  | .binary _ x y => x.inputs∪y.inputs
def registers (e : PolynomialExpression) (base : ℕ) : Finset ℕ :=
  e.inputs∪Finset.Ico base (base+e.nodes)

theorem evaluate_inputs_congr (e : PolynomialExpression) (v w : ℕ→ℚ)
    (same:∀i∈e.inputs,v i=w i) : e.evaluate v=e.evaluate w := by
  induction e with
  | literal => rfl
  | inputRegister i => exact same i (by simp [inputs])
  | binary op x y hx hy =>
    exact congrArg₂ (binaryValue op)
      (hx (fun i hi=>same i (Finset.mem_union_left _ hi)))
      (hy (fun i hi=>same i (Finset.mem_union_right _ hi)))

theorem instructions_valid_in (e : PolynomialExpression) (base : ℕ) (S : Finset ℕ)
    (source:e.inputs⊆S) (scratch:∀i,base ≤ i→i<base+e.nodes→i∈S) :
    ∀a∈e.instructions base,a.Valid S := by
  induction e generalizing base with
  | literal q =>
    simp only [instructions,List.mem_singleton,forall_eq,Instruction.Valid]
    exact scratch base le_rfl (by simp [nodes])
  | inputRegister i =>
    have input:i∈S:=source (by simp [inputs])
    have output:base∈S:=scratch base le_rfl (by simp [nodes])
    simp [instructions,Instruction.Valid,input,output]
  | binary op x y hx hy =>
    have nx:=x.nodes_pos
    have ny:=y.nodes_pos
    have sx:x.inputs⊆S:=fun _ h=>source (Finset.mem_union_left _ h)
    have sy:y.inputs⊆S:=fun _ h=>source (Finset.mem_union_right _ h)
    have vx:=hx base sx (fun i hi hj=>scratch i hi (by simp only [nodes];omega))
    have vy:=hy (base+1) sy (fun i hi hj=>scratch i (by omega) (by simp only [nodes];omega))
    intro a ha
    simp only [instructions,List.mem_append,List.mem_singleton] at ha
    rcases ha with (ha|ha)|rfl
    · exact vx a ha
    · exact vy a ha
    · exact ⟨scratch base le_rfl (by simp only [nodes];omega),
        scratch base le_rfl (by simp only [nodes];omega),
        scratch (base+1) (by omega) (by simp only [nodes];omega)⟩

theorem registers_valid (e : PolynomialExpression) (base : ℕ) :
    (e.control base).Valid (e.registers base) := by
  apply Control.prepend_valid
  · exact e.instructions_valid_in base _ (Finset.subset_union_left)
      (fun i hi hj=>Finset.mem_union_right _ (Finset.mem_Ico.mpr ⟨hi,hj⟩))
  · trivial

#print axioms registers_valid
end Maxwell.Continuum.RationalDataflow.PolynomialExpression
