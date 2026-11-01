import Maxwell.Continuum.MachinRuntimeCost
import Maxwell.Continuum.RationalDataflowRetainedCells
import Maxwell.Cost.Structured.NatAssign.Values

/-! The edge test's five scalar inputs are written from the actual Machin
words and bracket midpoint. No rational normalization is needed here. -/
namespace Maxwell.Continuum.Calibration.EdgeScalar
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
set_option maxHeartbeats 2200000
set_option maxRecDepth 16384

def saved : Finset ℕ := {232,233,234,235,236}
def outputPorts : Finset ℕ := ports saved
def midpointPorts : Finset ℕ := cellPorts 2302
def emitIds : Finset ℕ := Machin.allIds∪outputPorts∪midpointPorts
def emitPlan : List NatAssign.Instruction :=
  [.copy 623 1696,.copy 624 1697,.copy 625 1698,
   .copy 7906 1699,.copy 7907 1700,.copy 7908 1701,
   .literal 1702 7,.multiply 7908 1702,.add 1702 1699,
   .literal 1702 0,.literal 1703 0,.literal 1704 1,
   .literal 1705 0,.literal 1706 0,.literal 1707 1,
   .literal 1708 0,.literal 1709 0,.literal 1710 1]
def emitCode : Code := NatAssign.code emitPlan
def emitCost (B : ℕ) : ℕ := 3000*8^18*(B+2)^2
def emitWidth (B : ℕ) : ℕ := 2^18*(B+1)
def piParts (N : ℕ) : Parts :=
  ⟨Machin.numeratorPositive (N+7),Machin.numeratorNegative (N+7),Machin.commonDenominator (N+7)⟩
def result (N : ℕ) (p : Parts) (i : ℕ) : Parts :=
  if i=232 then piParts N else if i=233 then ⟨p.positive+7*p.denominator,p.negative,p.denominator⟩
  else Parts.literal 0
def emitInput (N : ℕ) (p : Parts) (old : ℕ→Parts) (i : ℕ) : ℕ :=
  if i∈Machin.allIds then Machin.finalValues (N+7) i
  else if i=7906 then p.positive else if i=7907 then p.negative else if i=7908 then p.denominator
  else dataValues old i

theorem emit_valid : ∀a∈emitPlan,a.Valid emitIds := by
  simp [emitPlan,NatAssign.Instruction.Valid,emitIds,Machin.allIds,RationalArctan.ids,
    outputPorts,ports,saved,cellPorts,positivePort,negativePort,denominatorPort,midpointPorts]

theorem emit_lower : ∀i∈emitIds,4≤ i := by
  intro i hi
  rcases Finset.mem_union.mp hi with other|mid
  · rcases Finset.mem_union.mp other with machin|output
    · exact Machin.allIds_ge i machin
    · exact ids_ge saved i (Finset.mem_union_left _ output)
  · simp only [midpointPorts,cellPorts,positivePort,negativePort,denominatorPort,
      Finset.mem_insert,Finset.mem_singleton] at mid
    omega

theorem emit_changes : NatAssign.changes emitPlan⊆{0,1,2,3}∪outputPorts := by
  decide +kernel

theorem emit_literals : ∀a∈emitPlan,a.literalWidth≤3 := by
  simp [emitPlan,NatAssign.Instruction.literalWidth]
  decide +kernel

theorem emit_result (N : ℕ) (p : Parts) (old : ℕ→Parts) (i : ℕ) (hi : i∈saved) :
    NatAssign.values emitPlan (emitInput N p old) (positivePort i)=(result N p i).positive ∧
    NatAssign.values emitPlan (emitInput N p old) (negativePort i)=(result N p i).negative ∧
    NatAssign.values emitPlan (emitInput N p old) (denominatorPort i)=(result N p i).denominator := by
  have h:=Machin.combine_values (N+7)
  simp only [saved,Finset.mem_insert,Finset.mem_singleton] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl <;>
    simp [emitPlan,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,
      NatAssign.Instruction.value,emitInput,result,piParts,positivePort,negativePort,denominatorPort,
      Machin.allIds,RationalArctan.ids,Machin.finalValues,h.1,h.2.1,h.2.2,Parts.literal]
  ring

theorem result_value (N : ℕ) (p : Parts) (positive : 0<p.denominator) :
    (result N p 232).value=piCenter (N+1) ∧ (result N p 233).value=p.value+7 ∧
      (∀i∈({234,235,236}:Finset ℕ),(result N p i).value=0) := by
  refine ⟨?_,?_,?_⟩
  · simpa only [result,ite_true,piParts,Parts.value,piCenter,Nat.add_assoc] using (Machin.piApprox_center (N+7)).symm
  · have nonzero : (p.denominator:ℚ)≠0 := by exact_mod_cast positive.ne'
    simp only [result,show (233:ℕ)≠232 from by decide,ite_false,ite_true,Parts.value,
      Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
    field_simp
    ring
  · intro i hi
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl|rfl|rfl <;> norm_num [result,Parts.literal,Parts.value]

theorem result_good (N : ℕ) (p : Parts) (positive : 0<p.denominator) : Good saved (result N p) := by
  intro i _
  unfold result
  split_ifs
  · exact Machin.commonDenominator_pos (N+7)
  · exact positive
  · exact Parts.literal_valid 0

theorem emit_executes (N : ℕ) (p : Parts) (old : ℕ→Parts) (B : ℕ) (hB : 3≤B)
    (width : ∀i∈emitIds,(emitInput N p old i).bits.length≤B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank emitIds (emitInput N p old) s.val) (scratch : NatAssign.Scratch s.val) :
    ∃steps t,Executes input tape emitCode steps s t ∧ steps≤emitCost B ∧
      Cells saved (result N p) t.val ∧ WidthBank saved (emitWidth B) (result N p) ∧
      NatAssign.Scratch t.val ∧ BinaryPrecision.Frame ({0,1,2,3}∪outputPorts) s.val t.val := by
  obtain ⟨c,t,e,charge,stored,blank,frame⟩:=NatAssign.executes emitIds emit_lower emitPlan emit_valid
    (emitInput N p old) input tape s bank scratch
  have cost:=NatAssign.price_bound emitIds emitPlan emit_valid (emitInput N p old) B width
    (fun a ha=>(emit_literals a ha).trans hB)
  have words:=NatAssign.values_width emitIds emitPlan emit_valid (emitInput N p old) B width
    (fun a ha=>(emit_literals a ha).trans hB)
  have member (i : ℕ) (hi : i∈saved) (k : ℕ) (hk : k∈cellPorts i) : k∈emitIds :=
    Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i,hi,hk⟩))
  refine ⟨c,t,e,charge.trans cost,?_,?_,blank,frame.mono emit_changes⟩
  · intro i hi
    have h:=emit_result N p old i hi
    exact ⟨h.1 ▸ stored _ (member i hi _ (by simp [cellPorts])),
      h.2.1 ▸ stored _ (member i hi _ (by simp [cellPorts,positivePort,negativePort])),
      h.2.2 ▸ stored _ (member i hi _ (by simp [cellPorts,positivePort,denominatorPort]))⟩
  · intro i hi
    have h:=emit_result N p old i hi
    exact ⟨h.1 ▸ Nat.le_of_succ_le (words _ (member i hi _ (by simp [cellPorts]))),
      h.2.1 ▸ Nat.le_of_succ_le (words _ (member i hi _ (by simp [cellPorts]))),
      h.2.2 ▸ Nat.le_of_succ_le (words _ (member i hi _ (by simp [cellPorts])))⟩

#print axioms emit_executes
end Maxwell.Continuum.Calibration.EdgeScalar
