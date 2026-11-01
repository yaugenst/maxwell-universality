import Maxwell.Cost.Structured.SignedBracketMachine
import Maxwell.Continuum.EdgeIntegerBracket
import Maxwell.Continuum.RationalDataflowRetainedCells

/-! Interpret the shared integer bracket machine as stored continuum edge
intervals. Only this adapter knows the rational register layout. -/
namespace Maxwell.Continuum.Calibration.EdgeBracketMachine
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
open Maxwell.Certificate
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384

def base : ℕ := positivePort 2300
def words (v : ℕ→ℕ) : EdgeWords :=
  ⟨(v base:ℤ)-v (base+1),(v (base+3):ℤ)-v (base+4),v (base+2)⟩
def parts (v : ℕ→ℕ) (i : ℕ) : Parts :=
  ⟨v (positivePort i),v (negativePort i),v (denominatorPort i)⟩
def Denominators (v : ℕ→ℕ) : Prop := 0<v (base+2) ∧ v (base+5)=v (base+2)

theorem bank_cells (v : ℕ→ℕ) (s : BitRAMState)
    (bank : NatAssign.Bank (SignedBracket.ids base) v s) : Cells {2300,2301,2302} (parts v) s := by
  intro i hi
  have range : 2300≤ i ∧ i≤2302 := by
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    omega
  have owned (k : ℕ) (hk : k∈cellPorts i) : k∈SignedBracket.ids base := by
    simp only [cellPorts,positivePort,negativePort,denominatorPort,Finset.mem_insert,Finset.mem_singleton] at hk
    simp only [SignedBracket.ids,Finset.mem_Ico,base,positivePort]
    omega
  exact ⟨bank _ (owned _ (by simp [cellPorts])),bank _ (owned _ (by simp [cellPorts,positivePort,negativePort])),
    bank _ (owned _ (by simp [cellPorts,positivePort,denominatorPort]))⟩

theorem parts_width (v : ℕ→ℕ) (B : ℕ)
    (width : ∀i∈SignedBracket.ids base,(v i).bits.length≤B) :
    WidthBank {2300,2301,2302} B (parts v) := by
  intro i hi
  have range : 2300≤ i ∧ i≤2302 := by
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    omega
  have owned (k : ℕ) (hk : k∈cellPorts i) : k∈SignedBracket.ids base := by
    simp only [cellPorts,positivePort,negativePort,denominatorPort,Finset.mem_insert,Finset.mem_singleton] at hk
    simp only [SignedBracket.ids,Finset.mem_Ico,base,positivePort]
    omega
  exact ⟨width _ (owned _ (by simp [cellPorts])),width _ (owned _ (by simp [cellPorts])),
    width _ (owned _ (by simp [cellPorts]))⟩

theorem endpoints (v : ℕ→ℕ) (den : Denominators v) :
    (parts v 2300).value=(words v).lo ∧ (parts v 2301).value=(words v).hi := by
  have d : v (denominatorPort 2301)=v (denominatorPort 2300) := den.2
  simp only [parts,Parts.value,words,EdgeWords.lo,EdgeWords.hi,Int.cast_sub,Int.cast_natCast]
  rw [d]
  exact ⟨rfl,rfl⟩

theorem midpoint_words (v : ℕ→ℕ) : words (NatAssign.values (SignedBracket.midpointPlan base) v)=words v := by
  have h0:=SignedBracket.midpoint_get base v 0 (by decide)
  simp only [Nat.add_zero] at h0
  unfold words
  rw [h0,SignedBracket.midpoint_get base v 1 (by decide),SignedBracket.midpoint_get base v 2 (by decide),
    SignedBracket.midpoint_get base v 3 (by decide),SignedBracket.midpoint_get base v 4 (by decide)]
  norm_num [SignedBracket.midpointValue]

theorem midpoint_value (v : ℕ→ℕ) :
    (parts (NatAssign.values (SignedBracket.midpointPlan base) v) 2302).value=(words v).midpoint := by
  change (((NatAssign.values (SignedBracket.midpointPlan base) v (base+6):ℕ):ℚ)-
    NatAssign.values (SignedBracket.midpointPlan base) v (base+7))/
      NatAssign.values (SignedBracket.midpointPlan base) v (base+8)=_
  rw [SignedBracket.midpoint_get base v 6 (by decide),SignedBracket.midpoint_get base v 7 (by decide),
    SignedBracket.midpoint_get base v 8 (by decide)]
  norm_num [SignedBracket.midpointValue,words,EdgeWords.midpoint]
  ring

theorem step_words (v : ℕ→ℕ) (negative : Bool) :
    words (NatAssign.values (SignedBracket.stepPlan base negative) v)=(words v).step negative := by
  have h0:=SignedBracket.step_get base negative v 0 (by decide)
  have h1:=SignedBracket.step_get base negative v 1 (by decide)
  have h2:=SignedBracket.step_get base negative v 2 (by decide)
  have h3:=SignedBracket.step_get base negative v 3 (by decide)
  have h4:=SignedBracket.step_get base negative v 4 (by decide)
  simp only [Nat.add_zero] at h0
  cases negative <;> simp only [words,EdgeWords.step,Bool.false_eq_true,ite_false,ite_true,
    h0,h1,h2,h3,h4,SignedBracket.stepValue] <;> norm_num <;> constructor <;> ring

theorem midpoint_denominators (v : ℕ→ℕ) (den : Denominators v) :
    Denominators (NatAssign.values (SignedBracket.midpointPlan base) v) := by
  simpa [Denominators,SignedBracket.midpoint_get base v 2 (by decide),
    SignedBracket.midpoint_get base v 5 (by decide),SignedBracket.midpointValue]
    using den

theorem step_denominators (v : ℕ→ℕ) (negative : Bool) (den : Denominators v) :
    Denominators (NatAssign.values (SignedBracket.stepPlan base negative) v) := by
  simp only [Denominators,SignedBracket.step_get base negative v 2 (by decide),
    SignedBracket.step_get base negative v 5 (by decide)]
  norm_num [SignedBracket.stepValue]
  exact den.1

#print axioms step_words
#print axioms midpoint_value
end Maxwell.Continuum.Calibration.EdgeBracketMachine
