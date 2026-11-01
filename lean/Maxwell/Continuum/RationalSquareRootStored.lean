import Maxwell.Continuum.RationalSquareRootSigned
import Maxwell.Continuum.RationalDataflowLayout
import Maxwell.Cost.Structured.NatAssign.Values

/-! An arbitrary finite square-root workspace is charged and reset before
loading a stored raw fraction and precision word. No fresh-scratch premise
is needed for the natural operand bank. -/
namespace Maxwell.Continuum.Calibration.RationalRoot.Stored
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
open RationalAccumulator (Word)
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

def ids (source : ℕ) : Finset ℕ := Raw.ids∪cellPorts source∪{700}
def sourceParts (source : ℕ) (n : ℕ→ℕ) : Parts :=
  ⟨n (positivePort source),n (negativePort source),n (denominatorPort source)⟩
def clearPlan : List NatAssign.Instruction :=
  (Raw.ids.sort (·≤·)).map (fun i=>.literal i 0)
def loadPlan (source : ℕ) : List NatAssign.Instruction :=
  [.copy (positivePort source) 30,.copy (negativePort source) 31,
   .copy (denominatorPort source) 229,.copy 700 544]
def plan (source : ℕ) : List NatAssign.Instruction := clearPlan++loadPlan source
def code (source : ℕ) : Code := .seq (NatAssign.code (plan source)) Signed.code
def costBound (source N W : ℕ) : ℕ :=
  3000*8^(plan source).length*(W+2)^2+Signed.costBound N W
def changed : Finset ℕ := {0,1,2,3}∪Raw.ids

theorem raw_ids_le (i : ℕ) (hi : i∈Raw.ids) : i≤548 := by
  simp only [Raw.ids,RationalRoot.ids,NaturalRoot.fullIds,NaturalRoot.ids,RationalCanonicalBank.ids,
    Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.mem_Icc] at hi
  omega

theorem ids_ge (source i : ℕ) (hi : i∈ids source) : 4 ≤ i := by
  rcases Finset.mem_union.mp hi with hi|hi
  · rcases Finset.mem_union.mp hi with hi|hi
    · exact Raw.ids_ge i hi
    · have hp:=positivePort_ge source
      have hm:=negativePort_ge source
      have hd:=denominatorPort_ge source
      simp only [cellPorts,Finset.mem_insert,Finset.mem_singleton] at hi
      omega
  · have : i=700 := by simpa using hi
    omega

theorem plan_valid (source : ℕ) : ∀a∈plan source,a.Valid (ids source) := by
  have hp:=positivePort_ge source
  have hm:=negativePort_ge source
  have hd:=denominatorPort_ge source
  intro a ha
  rcases List.mem_append.mp ha with ha|ha
  · obtain ⟨i,hi,rfl⟩:=List.mem_map.mp ha
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (by simpa only [Finset.mem_sort] using hi))
  · simp only [loadPlan,List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl|rfl <;>
      simp [NatAssign.Instruction.Valid,ids,cellPorts,Raw.ids,RationalRoot.ids,
        NaturalRoot.fullIds,NaturalRoot.ids,RationalCanonicalBank.ids] <;> omega

theorem clear_values (n : ℕ→ℕ) (i : ℕ) :
    NatAssign.values clearPlan n i=if i∈Raw.ids then 0 else n i := by
  simpa only [clearPlan,Finset.mem_sort] using
    NatAssign.values_literals (Raw.ids.sort (·≤·)) (fun _=>0) n i

theorem plan_values (source : ℕ) (n : ℕ→ℕ) (i : ℕ) (hi : i∈Raw.ids) :
    NatAssign.values (plan source) n i=Signed.inputValues (sourceParts source n) (n 700) i := by
  have hp:=positivePort_ge source
  have hm:=negativePort_ge source
  have hd:=denominatorPort_ge source
  have outp : positivePort source∉Raw.ids := fun h=>by have := raw_ids_le _ h; omega
  have outm : negativePort source∉Raw.ids := fun h=>by have := raw_ids_le _ h; omega
  have outd : denominatorPort source∉Raw.ids := fun h=>by have := raw_ids_le _ h; omega
  have outN : 700∉Raw.ids := fun h=>by have := raw_ids_le _ h; omega
  have ne : positivePort source≠30 ∧ negativePort source≠30 ∧ negativePort source≠31 ∧
      denominatorPort source≠30 ∧ denominatorPort source≠31 := by omega
  simp only [plan,NatAssign.values_append]
  simp [loadPlan,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.value,
    NatAssign.Instruction.target,Signed.inputValues,sourceParts,Raw.inputValues,
    RationalCanonicalBank.inputValues,clear_values,outp,outm,outd,outN,ne]
  split_ifs <;> simp_all [clear_values]

theorem plan_changes (source : ℕ) : NatAssign.changes (plan source)⊆changed := by
  intro i hi
  rcases Finset.mem_union.mp hi with hi|hi
  · exact Finset.mem_union_left _ hi
  · obtain ⟨a,ha,eq⟩:=List.mem_map.mp (List.mem_toFinset.mp hi)
    apply Finset.mem_union_right
    rcases List.mem_append.mp ha with ha|ha
    · obtain ⟨j,hj,rfl⟩:=List.mem_map.mp ha
      exact eq ▸ (by simpa only [Finset.mem_sort,NatAssign.Instruction.target] using hj)
    · simp only [loadPlan,List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl|rfl|rfl|rfl <;> subst i <;>
        simp only [NatAssign.Instruction.target] <;> decide

theorem executes (source : ℕ) (n : ℕ→ℕ) (W : ℕ)
    (width : ∀i∈ids source,(n i).bits.length≤W)
    (valid : (sourceParts source n).Valid) (nonnegative : 0≤(sourceParts source n).value)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank (ids source) n s.val) (scratch : NatAssign.Scratch s.val) :
    ∃cost t num den,Executes input tape (code source) cost s t ∧ cost≤costBound source (n 700) W ∧
      Word t.val 32 num ∧ Word t.val 548 den ∧ 0<den ∧
      (num:ℚ)/den=sqrtRationalCenter (sourceParts source n).value (n 700) ∧
      NatAssign.Bank Raw.ids (Raw.outputValues
        (IntegerNormSquare.magnitude (sourceParts source n).positive (sourceParts source n).negative)
        (sourceParts source n).denominator (n 700)) t.val ∧
      NatAssign.Scratch t.val ∧ BinaryPrecision.Frame changed s.val t.val := by
  obtain ⟨c0,u,e0,h0,b0,z0,f0⟩ := NatAssign.executes (ids source) (ids_ge source)
    (plan source) (plan_valid source) n input tape s bank scratch
  have literals : ∀a∈plan source,a.literalWidth≤W := by
    intro a ha
    rcases List.mem_append.mp ha with ha|ha
    · obtain ⟨i,_,rfl⟩:=List.mem_map.mp ha
      exact Nat.zero_le _
    · simp only [loadPlan,List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl|rfl|rfl|rfl <;> exact Nat.zero_le _
  have price := NatAssign.price_bound (ids source) (plan source) (plan_valid source) n W width literals
  have prepared : NatAssign.Bank Raw.ids (Signed.inputValues (sourceParts source n) (n 700)) u.val := by
    intro i hi
    rw [←plan_values source n i hi]
    exact b0 i (Finset.mem_union_left _ (Finset.mem_union_left _ hi))
  have hw : (sourceParts source n).Width W := by
    refine ⟨width _ ?_,width _ ?_,width _ ?_⟩ <;> simp [ids,cellPorts]
  obtain ⟨c1,t,num,den,e1,h1,wn,wd,pos,value,bt,zt,f1⟩ := Signed.executes
    (sourceParts source n) (n 700) W valid nonnegative hw (width 700 (by simp [ids]))
    input tape u prepared z0
  exact ⟨c0+c1,t,num,den,e0.seq e1,Nat.add_le_add (h0.trans price) h1,wn,wd,pos,value,bt,zt,
    (f0.mono (plan_changes source)).trans (f1.mono (by decide))⟩

#print axioms executes
end Maxwell.Continuum.Calibration.RationalRoot.Stored
