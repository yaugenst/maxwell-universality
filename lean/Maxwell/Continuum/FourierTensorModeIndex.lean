import Maxwell.Continuum.FourierTensorModeRows
import Maxwell.Continuum.RationalDataflowIndexArithmetic
import Maxwell.Continuum.NatAssignOutputWidth

/-! Runtime indices for a component's real and imaginary Fourier entries.
Only the choice among the three components is a fixed program parameter;
the row, radius, and full array length are actually stored words. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime.ModeIndex
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
open RationalAccumulator (Word Blank)
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

def ports : Finset ℕ := Finset.Icc 310 322
def changed : Finset ℕ := {0,1,2,3}∪ports
def initial (R size row : ℕ) (i : ℕ) : ℕ :=
  if i=310 then row else if i=311 then R else if i=322 then size else 0

def instructions (j : Fin 3) : List NatAssign.Instruction :=
  [.literal 312 3,.multiply 312 310,.literal 313 j.val,.add 313 310,
   .copy 310 321,.add 322 321]

def code (j : Fin 3) : Code :=
  .seq (PartArray.RowIndex.cloneCanonicalCode 201 310) (NatAssign.code (instructions j))

def values (j : Fin 3) (R size row : ℕ) : ℕ→ℕ :=
  NatAssign.values (instructions j) (initial R size row)

theorem valid (j : Fin 3) : ∀a∈instructions j,a.Valid ports := by
  simp [instructions,NatAssign.Instruction.Valid,ports]

theorem values_real (j : Fin 3) (R size row : ℕ) : values j R size row 310=3*row+j.val := by
  simp [values,instructions,initial,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,NatAssign.Instruction.value,Nat.mul_comm,Nat.add_comm]

theorem values_imag (j : Fin 3) (R size row : ℕ) : values j R size row 321=size+(3*row+j.val) := by
  simp [values,instructions,initial,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,NatAssign.Instruction.value,Nat.mul_comm,Nat.add_comm]

theorem values_radius (j : Fin 3) (R size row : ℕ) : values j R size row 311=R := by
  simp [values,instructions,initial,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,NatAssign.Instruction.value]

theorem initial_width (R size row W : ℕ) (hR : R.bits.length≤W)
    (hsize : size.bits.length≤W) (hr : row.bits.length≤W) :
    ∀i∈ports,(initial R size row i).bits.length≤W := by
  intro i _
  unfold initial
  split_ifs <;> first | exact hr | exact hR | exact hsize | simp

theorem executes (j : Fin 3) (R size W : ℕ) (hW : 2≤W)
    (hR : R.bits.length≤W) (hsize : size.bits.length≤W)
    (input : List Bool) (tape : ℕ→Bool) (word : List Bool) (hlen : word.length≤W)
    (s : Store) (hc : BankArray.Word s.val 201 word)
    (hb : NatAssign.Bank ports (initial R size 0) s.val) (hz : NatAssign.Scratch s.val) :
    ∃cost t,Executes input tape (code j) cost s t ∧ cost≤2^34*(W+5)^2 ∧
      NatAssign.Bank ports (values j R size (addressValue word)) t.val ∧
      (∀i∈ports,(values j R size (addressValue word) i).bits.length≤64*(W+1)) ∧
      NatAssign.Scratch t.val ∧ BinaryPrecision.Frame changed s.val t.val := by
  have hzero : Blank s.val 310 := by
    exact (RationalAccumulator.zero_word_iff_blank _ _).mp (hb 310 (by simp [ports]))
  obtain ⟨c0,s0,e0,hc0,b0,f0⟩ := PartArray.RowIndex.cloneCanonical_executes 201 310
    (by decide) input tape word s hc hzero
  have hr : (addressValue word).bits.length≤W := by
    apply le_trans _ hlen
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr (Subtraction.addressValue_lt_pow_length word)
  have bank0 : NatAssign.Bank ports (initial R size (addressValue word)) s0.val := by
    intro i hi
    by_cases h310 : i=310
    · subst i
      simpa only [initial,ite_true] using b0
    · have h := RationalAccumulator.word_of_eq (f0.tapes i (by simpa using h310)) (hb i hi)
      simpa only [initial,ite_eq_right h310] using h
  have z0 : NatAssign.Scratch s0.val := by
    intro i hi
    exact RationalAccumulator.blank_of_eq (f0.tapes i (by simp only [Finset.mem_singleton];omega)) (hz i hi)
  obtain ⟨c1,t,e1,hc1,b1,z1,f1⟩ := NatAssign.executes ports
    (fun i hi => by simp only [ports,Finset.mem_Icc] at hi;omega)
    (instructions j) (valid j) (initial R size (addressValue word)) input tape s0 bank0 z0
  have literals : ∀a∈instructions j,a.literalWidth≤W := by
    have hj : j.val.bits.length≤2 := by
      have h := RationalWords.bits_mono (show j.val≤2 by omega)
      exact h.trans (by decide)
    simp [instructions,NatAssign.Instruction.literalWidth]
    exact ⟨hW,hj.trans hW⟩
  have wi := initial_width R size (addressValue word) W hR hsize hr
  have price := hc1.trans (NatAssign.price_bound ports (instructions j) (valid j)
    (initial R size (addressValue word)) W wi literals)
  have width := NatAssign.values_width_bound ports (instructions j) (valid j)
    (initial R size (addressValue word)) W wi literals
  refine ⟨c0+c1,t,e0.seq e1,?_,b1,?_,z1,(f0.mono ?_).trans (f1.mono ?_)⟩
  · simp only [instructions,List.length_cons,List.length_nil] at price
    norm_num at price
    nlinarith only [hc0,price,hlen,Nat.zero_le W]
  · intro i hi
    have h := width i hi
    simp only [instructions,List.length_cons,List.length_nil] at h
    exact Nat.le_of_succ_le (show (values j R size (addressValue word) i).bits.length+1≤64*(W+1) from h)
  · simp only [Finset.singleton_subset_iff,changed,Finset.mem_union,ports,Finset.mem_Icc]
    exact Or.inr (by omega)
  · intro i hi
    simp only [NatAssign.changes,instructions,NatAssign.Instruction.target,List.map_cons,List.map_nil,
      List.toFinset_cons,List.toFinset_nil,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,
      Finset.notMem_empty,or_false] at hi
    simp only [changed,ports,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.mem_Icc]
    omega

#print axioms executes
end Maxwell.Continuum.Profile.WaveMachine.Runtime.ModeIndex
