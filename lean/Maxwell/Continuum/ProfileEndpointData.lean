import Maxwell.Continuum.ProfileEndpointMoments
import Maxwell.Continuum.ProfileDFTInitializationData
import Maxwell.Continuum.RationalDataflowIntegerWidths
import Maxwell.Continuum.RationalDataflowArrayProgram
import Maxwell.Continuum.RationalDataflowArraySum

/-! The fixed five-addition endpoint moment kernel and its linear raw-word
growth. All coefficients and moments remain denominator-one integers. -/
namespace Maxwell.Continuum.Profile.Runtime
open RationalDataflow Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 2500000

def endpointBody : List Instruction :=
  [.binary .add 4 2 2,.binary .add 3 3 4,.binary .add 3 3 0,
   .binary .add 2 2 0,.binary .add 0 0 1]
def endpointStep (v : ℕ→Parts) : ℕ→Parts := evaluate endpointBody v
def endpointValues {n : ℕ} (a : PartArray.Table n) (v : ℕ→Parts) (k : ℕ) : ℕ→Parts :=
  PartArray.programIterate a 1 endpointStep v k
def endpointLoaded {n : ℕ} (a : PartArray.Table n) (v : ℕ→Parts) (k : ℕ) : ℕ→Parts :=
  PartArray.programLoaded a 1 endpointStep v k
def endpointCode : Code := PartArray.programCode 1 (program endpointBody)

theorem endpointBody_valid : ∀a∈endpointBody,a.Valid dftRegisters := by
  simp only [endpointBody,List.mem_cons,List.not_mem_nil,or_false]
  intro a ha
  rcases ha with rfl|rfl|rfl|rfl|rfl <;> simp [Instruction.Valid,dftRegisters]

theorem endpointBody_additions : ∀a∈endpointBody,∃t l r,
    a=Instruction.binary .add t l r ∧ l∈dftRegisters ∧ r∈dftRegisters := by
  simp only [endpointBody,List.mem_cons,List.not_mem_nil,or_false]
  intro a ha
  rcases ha with rfl|rfl|rfl|rfl|rfl
  · exact ⟨4,2,2,rfl,by decide,by decide⟩
  · exact ⟨3,3,4,rfl,by decide,by decide⟩
  · exact ⟨3,3,0,rfl,by decide,by decide⟩
  · exact ⟨2,2,0,rfl,by decide,by decide⟩
  · exact ⟨0,0,1,rfl,by decide,by decide⟩

theorem endpointStep_trace (v : ℕ→Parts) (B : ℕ)
    (hv : IntegerBank dftRegisters v) (hw : WidthBank dftRegisters B v) :
    IntegerBank dftRegisters (endpointStep v) ∧
    WidthBank dftRegisters (B+5) (endpointStep v) ∧
    WidthTrace dftRegisters (B+5) endpointBody v := by
  simpa only [endpointBody,List.length_cons,List.length_nil,endpointStep] using
    additions_trace dftRegisters endpointBody endpointBody_additions v B hv hw

theorem endpointStep_values (v : ℕ→Parts) (hv : Good dftRegisters v) :
    (endpointStep v 0).value=(v 0).value+(v 1).value ∧
    (endpointStep v 2).value=(v 2).value+(v 0).value ∧
    (endpointStep v 3).value=(v 3).value+2*(v 2).value+(v 0).value := by
  have h0 := hv 0 (by decide)
  have h1 := hv 1 (by decide)
  have h2 := hv 2 (by decide)
  have h3 := hv 3 (by decide)
  simp only [endpointStep,endpointBody,evaluate,Instruction.update,BinaryOp.eval,
    Function.update_self,Function.update_of_ne (by decide : (0:ℕ)≠2),
    Function.update_of_ne (by decide : (0:ℕ)≠3),
    Function.update_of_ne (by decide : (0:ℕ)≠4),
    Function.update_of_ne (by decide : (1:ℕ)≠2),
    Function.update_of_ne (by decide : (1:ℕ)≠3),
    Function.update_of_ne (by decide : (1:ℕ)≠4),
    Function.update_of_ne (by decide : (2:ℕ)≠0),
    Function.update_of_ne (by decide : (2:ℕ)≠3),
    Function.update_of_ne (by decide : (2:ℕ)≠4),
    Function.update_of_ne (by decide : (3:ℕ)≠0),
    Function.update_of_ne (by decide : (3:ℕ)≠2),
    Function.update_of_ne (by decide : (3:ℕ)≠4)]
  rw [Parts.add_value _ _ h0 h1,Parts.add_value _ _ h2 h0,
    Parts.add_value _ _ (Parts.add_valid h3 (Parts.add_valid h2 h2)) h0,
    Parts.add_value _ _ h3 (Parts.add_valid h2 h2),Parts.add_value _ _ h2 h2]
  exact ⟨rfl,rfl,by ring⟩

theorem endpointValues_width {n : ℕ} (a : PartArray.Table n) (v : ℕ→Parts) (B : ℕ)
    (hB : 1≤B) (ha : ∀i,(a.get i).Width B) (hd : ∀i,(a.get i).denominator=1)
    (hv : IntegerBank dftRegisters v) (hw : WidthBank dftRegisters B v)
    (k : ℕ) (hk : k≤n) :
    IntegerBank dftRegisters (endpointValues a v k) ∧
    WidthBank dftRegisters (B+5*k) (endpointValues a v k) := by
  induction k with
  | zero => exact ⟨hv,by simpa [endpointValues,PartArray.programIterate] using hw⟩
  | succ k ih =>
    obtain ⟨hg,hn⟩ := ih (by omega)
    have hi : n-1-k<n := by omega
    have he : a.getD (n-1-k)=a.get ⟨n-1-k,hi⟩ := by
      simp only [PartArray.Table.getD,dite_eq_left hi]
    have hl : IntegerBank dftRegisters (endpointLoaded a v k) := hg.update 1 (by rw [he];exact hd _)
    have hwl : WidthBank dftRegisters (B+5*k) (endpointLoaded a v k) :=
      hn.update 1 ((a.getD_width B hB ha _).mono (by omega))
    obtain ⟨hg',hn',_⟩ := endpointStep_trace _ _ hl hwl
    refine ⟨hg',?_⟩
    change WidthBank dftRegisters (B+5*(k+1)) (endpointStep (endpointLoaded a v k))
    simpa only [Nat.mul_add,Nat.mul_one,Nat.add_assoc] using hn'

#print axioms endpointStep_values
#print axioms endpointValues_width
end Maxwell.Continuum.Profile.Runtime
