import Maxwell.Continuum.RationalDataflowMatrixTapeBound
import Maxwell.Continuum.RationalDataflowInitialize
import Maxwell.Cost.Structured.TapeBlockSwapFrame

/-! The central matrix circuit owns a separate fixed tape interval. Its
large symbolic register bank cannot overwrite retained calibration words. -/
namespace Maxwell.Continuum.Calibration.CentralRelocation
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
open RationalAccumulator (Blank)
set_option maxHeartbeats 1500000
set_option maxRecDepth 16384

def count : ℕ := MatrixInverse.tapeBound 24+10000
def gap : ℕ := count+10000
def relocation : Equiv.Perm ℕ := TapeBlockSwap.permutation 4 count gap (by unfold gap;omega)
def bank : Finset ℕ := MatrixInverse.registers 24
def work : Finset ℕ := (workspace bank).image relocation
def initializeCode : Code := .call ((Initialize.code bank).compile.renameTapes relocation)

attribute [local irreducible] bank count MatrixInverse.registers MatrixInverse.tapeBound
  PolynomialExpression.determinantNodes

theorem relocation_involutive (i : ℕ) : relocation (relocation i)=i :=
  TapeBlockSwap.involutive 4 count gap (by unfold gap;omega) i

theorem bank_bound : ∀i∈ids bank,i<count := by
  intro i hi
  have sourceBound : ∀j∈bank,j<MatrixInverse.base 24+2*PolynomialExpression.determinantNodes 24 1+3 := by
    intro j hj
    simpa only [bank,MatrixInverse.registers,Finset.mem_range] using hj
  have h:=ids_bound bank _ sourceBound i hi
  have h' : i<MatrixInverse.tapeBound 24 := by simpa only [MatrixInverse.tapeBound] using h
  unfold count
  exact h'.trans_le (Nat.le_add_right _ _)

theorem work_bound : ∀i∈workspace bank,i<count := by
  intro i hi
  rcases Finset.mem_union.mp hi with low | high
  · simp only [Finset.mem_insert,Finset.mem_singleton] at low
    unfold count
    omega
  · exact bank_bound i high

theorem moved (i : ℕ) (lo : 4≤ i) (hi : i<count) : relocation i=i+gap :=
  TapeBlockSwap.apply_inside 4 count gap _ i lo (by omega)

theorem scratch_fixed (i : ℕ) (hi : i<4) : relocation i=i :=
  TapeBlockSwap.apply_outside 4 count gap _ i (Or.inl hi) (Or.inl (by omega))

theorem state_tape (s : Store) (i : ℕ) :
    (s.renameTapes relocation).val.tapes i=s.val.tapes (relocation i) := by
  simp only [Store.renameTapes,BitRAMState.renameTapes,Function.comp_apply,relocation,TapeBlockSwap.symm]

theorem twice (s : Store) : (s.renameTapes relocation).renameTapes relocation=s :=
  Store.renameTapes_symm relocation s

theorem retained {s t : BitRAMState} (frame : BinaryPrecision.Frame work s t)
    (i : ℕ) (lo : 4≤ i) (hi : i<count) : t.tapes i=s.tapes i := by
  apply TapeBlockSwap.retained (show count≤gap by unfold gap;omega) (workspace bank) ?_ frame i lo (by omega)
  intro j hj
  have h:=work_bound j hj
  unfold gap
  exact h.trans_le ((Nat.le_add_right count 10000).trans (Nat.le_add_left _ 4))

theorem initialize_executes (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (fresh : ∀i,gap≤ i→Blank s.val i) (scratch : NatAssign.Scratch s.val) :
    ∃steps t,Executes input tape initializeCode steps s t ∧ steps≤Initialize.cost bank+1 ∧
      Ready bank Initialize.parts (t.renameTapes relocation) ∧
      BinaryPrecision.Frame work s.val t.val := by
  have blank : ∀i∈ids bank,Blank (s.renameTapes relocation).val i := by
    intro i hi
    obtain ⟨origin,word⟩:=fresh (i+gap) (by omega)
    refine ⟨origin,?_⟩
    rw [state_tape,moved i (ids_ge bank i hi) (bank_bound i hi)]
    exact word
  have clear : NatAssign.Scratch (s.renameTapes relocation).val := by
    intro i hi
    exact RationalAccumulator.blank_of_eq ((state_tape s i).trans (congrArg s.val.tapes (scratch_fixed i hi)))
      (scratch i hi)
  obtain ⟨steps,a,execution,charge,ready,frame⟩:=Initialize.executes bank input tape
    (s.renameTapes relocation) blank clear
  refine ⟨steps+1,a.renameTapes relocation,?_,Nat.add_le_add_right charge 1,?_,?_⟩
  · simpa only [initializeCode,twice] using execution.renamed_call relocation
  · simpa only [twice] using ready
  · have hf:=frame.renameTapes relocation
    have eq:=congrArg Subtype.val (twice s)
    exact eq ▸ hf

#print axioms initialize_executes
end Maxwell.Continuum.Calibration.CentralRelocation
