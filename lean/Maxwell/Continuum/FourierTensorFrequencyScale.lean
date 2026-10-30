import Maxwell.Continuum.FourierTensorPhysicalFactorShared

/-! The angular-frequency scale is computed from the literal stored
length and supercell size. The factor two is part of the executed code. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime.FrequencyScaleMachine
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
open RationalAccumulator (Word Blank)
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

def extra : Finset ℕ := {350,352,353}
def allIds (S : Finset ℕ) : Finset ℕ := RationalDataflow.ids S∪extra
def workspace (S : Finset ℕ) : Finset ℕ := {0,1,2,3}∪allIds S
def parameters (M L : ℕ) (v : ℕ→ℕ) : ℕ→ℕ :=
  Function.update (Function.update (Function.update v 350 M) 352 L) 353 0
def initial (M L : ℕ) (v : ℕ→Parts) : ℕ→ℕ := parameters M L (dataValues v)
def result (M L : ℕ) : Parts := ⟨L,0,2*M⟩
def instructions (target : ℕ) : List NatAssign.Instruction :=
  [.copy 352 (positivePort target),.literal (negativePort target) 0,
   .copy 350 (denominatorPort target),.literal 353 2,.multiply 353 (denominatorPort target),.literal 353 0]
def code (target : ℕ) : Code := NatAssign.code (instructions target)

theorem result_value (M L : ℕ) : (result M L).value=(L:ℚ)/(2*M) := by simp [result,Parts.value]
theorem result_valid (M L : ℕ) (hM : 0<M) : (result M L).Valid := by change 0<2*M;omega

theorem extras_small (i : ℕ) (hi : i∈extra) : 350 ≤ i ∧ i ≤ 353 := by
  simp only [extra,Finset.mem_insert,Finset.mem_singleton] at hi
  omega

theorem extras_outside (S : Finset ℕ) (i : ℕ) (hi : i∈extra) : i∉RationalDataflow.ids S := by
  have hh := extras_small i hi
  intro hm
  rcases Finset.mem_union.mp hm with hm|hm
  · obtain ⟨r,_,hr⟩ := Finset.mem_biUnion.mp hm
    have hp := positivePort_ge r
    have hn := negativePort_ge r
    have hd := denominatorPort_ge r
    simp only [cellPorts,Finset.mem_insert,Finset.mem_singleton] at hr
    omega
  · simp only [workPorts,temporaryPorts,RationalMagnitude.ids,Finset.mem_union,
      Finset.mem_insert,Finset.mem_singleton] at hm
    omega

theorem ids_ge (S : Finset ℕ) (i : ℕ) (hi : i∈allIds S) : 4 ≤ i := by
  rcases Finset.mem_union.mp hi with hi|hi
  · exact RationalDataflow.ids_ge S i hi
  · have := extras_small i hi;omega

theorem valid (S : Finset ℕ) (target : ℕ) (ht : target∈S) :
    ∀a∈instructions target,a.Valid (allIds S) := by
  have hp := Finset.mem_union_left extra
    (cell_mem ht (show positivePort target∈cellPorts target by simp [cellPorts]))
  have hn := Finset.mem_union_left extra
    (cell_mem ht (show negativePort target∈cellPorts target by simp [cellPorts]))
  have hd := Finset.mem_union_left extra
    (cell_mem ht (show denominatorPort target∈cellPorts target by simp [cellPorts]))
  have h350 : 350∈allIds S := Finset.mem_union_right _ (by decide)
  have h352 : 352∈allIds S := Finset.mem_union_right _ (by decide)
  have h353 : 353∈allIds S := Finset.mem_union_right _ (by decide)
  have hpg := positivePort_ge target
  have hdg := denominatorPort_ge target
  intro a ha
  simp only [instructions,List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with rfl|rfl|rfl|rfl|rfl|rfl
  · exact ⟨h352,hp,by omega⟩
  · exact hn
  · exact ⟨h350,hd,by omega⟩
  · exact h353
  · exact ⟨h353,hd,by omega⟩
  · exact h353

theorem values (M L : ℕ) (v : ℕ→Parts) (target : ℕ) :
    NatAssign.values (instructions target) (initial M L v)=initial M L (Function.update v target (result M L)) := by
  simp only [initial]
  rw [←writeParts_dataValues]
  have hp := positivePort_ge target
  have hn := negativePort_ge target
  have hd := denominatorPort_ge target
  ext i
  simp (disch := omega) [instructions,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.value,NatAssign.Instruction.target,parameters,writeParts,result]
  simp only [Function.update_apply]
  split_ifs <;> first | rfl | omega

theorem initial_bank (S : Finset ℕ) (M L : ℕ) (v : ℕ→Parts) (s : Store)
    (hr : Ready S v s) (hm : Word s.val 350 M) (hl : Word s.val 352 L) (hz : Blank s.val 353) :
    NatAssign.Bank (allIds S) (initial M L v) s.val := by
  intro i hi
  by_cases h350 : i=350
  · subst i;simpa [initial,parameters] using hm
  by_cases h352 : i=352
  · subst i;simpa [initial,parameters] using hl
  by_cases h353 : i=353
  · subst i;simpa [initial,parameters] using (RationalAccumulator.zero_word_iff_blank s.val 353).mpr hz
  have hi' : i∈RationalDataflow.ids S := (Finset.mem_union.mp hi).resolve_right (by simp [extra,h350,h352,h353])
  simpa only [initial,parameters,Function.update_of_ne h350,Function.update_of_ne h352,
    Function.update_of_ne h353] using hr.1 i hi'

theorem initial_width (S : Finset ℕ) (M L W : ℕ) (v : ℕ→Parts)
    (hw : WidthBank S W v) (hm : M.bits.length≤W) (hl : L.bits.length≤W)
    (i : ℕ) (hi : i∈allIds S) : (initial M L v i).bits.length≤W := by
  by_cases h350 : i=350
  · subst i;simpa [initial,parameters] using hm
  by_cases h352 : i=352
  · subst i;simpa [initial,parameters] using hl
  by_cases h353 : i=353
  · subst i;simp [initial,parameters]
  have hi' : i∈RationalDataflow.ids S := (Finset.mem_union.mp hi).resolve_right (by simp [extra,h350,h352,h353])
  simpa only [initial,parameters,Function.update_of_ne h350,Function.update_of_ne h352,
    Function.update_of_ne h353] using dataValues_width S v W hw i hi'

theorem executes (S : Finset ℕ) (target M L W : ℕ) (v : ℕ→Parts) (ht : target∈S)
    (hW : 2≤W) (hw : WidthBank S W v) (hm : M.bits.length≤W) (hl : L.bits.length≤W)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hr : Ready S v s) (wm : Word s.val 350 M) (wl : Word s.val 352 L) (hz : Blank s.val 353) :
    ∃cost t,Executes input tape (code target) cost s t ∧ cost≤stageCost W ∧
      Ready S (Function.update v target (result M L)) t ∧
      Word t.val 350 M ∧ Word t.val 352 L ∧ Blank t.val 353 ∧
      BinaryPrecision.Frame (workspace S) s.val t.val := by
  obtain ⟨c,t,e,hc,b,z,f⟩ := fixedBankStage_executes (allIds S) (ids_ge S)
    (instructions target) (valid S target ht) (by simp [instructions])
    (initial M L v) W (initial_width S M L W v hw hm hl)
    (by simp [instructions,NatAssign.Instruction.literalWidth,show (2:ℕ).bits.length=2 by decide];exact hW)
    input tape s (initial_bank S M L v s hr wm wl hz) hr.2
  rw [values] at b
  refine ⟨c,t,e,hc,⟨?_,z⟩,?_,?_,?_,f⟩
  · intro i hi
    have h350 : i≠350 := fun he => extras_outside S i (by simp [he,extra]) hi
    have h352 : i≠352 := fun he => extras_outside S i (by simp [he,extra]) hi
    have h353 : i≠353 := fun he => extras_outside S i (by simp [he,extra]) hi
    simpa only [initial,parameters,Function.update_of_ne h350,Function.update_of_ne h352,
      Function.update_of_ne h353] using b i (Finset.mem_union_left _ hi)
  · simpa [initial,parameters] using b 350 (Finset.mem_union_right _ (by decide))
  · simpa [initial,parameters] using b 352 (Finset.mem_union_right _ (by decide))
  · apply (RationalAccumulator.zero_word_iff_blank _ _).mp
    simpa [initial,parameters] using b 353 (Finset.mem_union_right _ (by decide))

#print axioms executes
#print axioms result_value
end Maxwell.Continuum.Profile.WaveMachine.Runtime.FrequencyScaleMachine
