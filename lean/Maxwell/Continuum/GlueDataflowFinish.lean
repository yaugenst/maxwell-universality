import Maxwell.Continuum.GlueDataflowStages
import Maxwell.Cost.Structured.RegisterFootprint

/-! Exact output, preserved precision, raw sizes and cleanup for the fixed glue call. -/
namespace Maxwell.Continuum.RationalDataflow.Glue
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 3500000
set_option maxRecDepth 8192

def workWidth (N W : ℕ) : ℕ := 2^32*(N+W+9)^4

theorem core_precision (a b N : ℕ) : GlueMachine.Runtime.finalValues a b N 640=N := by
  unfold GlueMachine.Runtime.finalValues
  split_ifs
  · simpa [GlueMachine.Runtime.zeroValues,GlueMachine.writeZero,NatAssign.values,
      NatAssign.Instruction.update,NatAssign.Instruction.target,NatAssign.Instruction.value]
      using (GlueMachine.Runtime.comparisonValues_saved a b N).1
  · simpa only [GlueMachine.Runtime.expFinalValues,
      show ¬640∈RationalTaylor.Runtime.ids by decide,ite_false]
      using (GlueMachine.Runtime.preparedValues_saved a b N).1

theorem core_width (a b N W : ℕ) (ha : a.bits.length≤W) (hb : b.bits.length≤W)
    (hN : N.bits.length≤W) (hW : 4≤W) (i : ℕ) (hi : i∈GlueMachine.Runtime.ids) :
    (GlueMachine.Runtime.finalValues a b N i).bits.length≤2^30*(N+W+8)^4 := by
  unfold GlueMachine.Runtime.finalValues
  split_ifs
  · have hv : ∀a∈GlueMachine.writeZero,a.Valid GlueMachine.Runtime.ids := by
      simp [GlueMachine.writeZero,NatAssign.Instruction.Valid,GlueMachine.Runtime.ids,
        GlueMachine.ids,GlueMachine.extra,SelectedParameters.Compare.ids,RationalTaylor.ids]
    have hw := NatAssign.values_width_bound GlueMachine.Runtime.ids GlueMachine.writeZero hv
      (GlueMachine.Runtime.comparisonValues a b N) (GlueMachine.Runtime.setupWidth W)
      (GlueMachine.Runtime.comparisonValues_width a b N W ha hb hN hW)
      (by simp [GlueMachine.writeZero,NatAssign.Instruction.literalWidth,GlueMachine.Runtime.setupWidth];omega)
      i hi
    have hx : W+1≤(N+W+8)^4 := (show W+1≤N+W+8 by omega).trans (Nat.le_self_pow (by decide) _)
    change (GlueMachine.Runtime.zeroValues a b N i).bits.length≤_
    exact (Nat.le_succ _).trans (hw.trans (by
      change 2^3*(GlueMachine.Runtime.setupWidth W+1)≤_
      unfold GlueMachine.Runtime.setupWidth
      nlinarith only [hx]))
  · exact (GlueMachine.Runtime.expFinalValues_width a b N W ha hb hN hW i hi).trans
      ((GlueMachine.Runtime.resultWidth_bound N W).trans (Nat.mul_le_mul_right _ (by norm_num)))

theorem unsignedFinished_precision (N : ℕ) (v : ℕ→Parts) (source : ℕ) :
    unsignedFinished N v source 640=N := by
  simp only [unsignedFinished,Function.update_of_ne (by decide : (640:ℕ)≠641),returned,
    show 640∈GlueMachine.Runtime.ids by decide,ite_true,core_precision]

theorem unsignedFinished_output (N : ℕ) (v : ℕ→Parts) (source : ℕ) :
    (⟨unsignedFinished N v source 602,unsignedFinished N v source 603,
      unsignedFinished N v source 604⟩ : Parts)=
      GlueMachine.Runtime.result (Phase.magnitude (v source)) (v source).denominator N := by
  have h := GlueMachine.Runtime.finalValues_output (Phase.magnitude (v source)) (v source).denominator N
  simp only [unsignedFinished,Function.update_of_ne (by decide : (602:ℕ)≠641),
    Function.update_of_ne (by decide : (603:ℕ)≠641),Function.update_of_ne (by decide : (604:ℕ)≠641),
    returned,show 602∈GlueMachine.Runtime.ids by decide,show 603∈GlueMachine.Runtime.ids by decide,
    show 604∈GlueMachine.Runtime.ids by decide,ite_true,h.1,h.2.1,h.2.2]

theorem corrected_output (N : ℕ) (v : ℕ→Parts) (source : ℕ) :
    (⟨corrected N v source 602,corrected N v source 603,corrected N v source 604⟩ : Parts)=
      result N (v source) := by
  unfold corrected result
  split_ifs
  · simp [GlueMachine.writeZero,NatAssign.values,NatAssign.Instruction.update,
      NatAssign.Instruction.target,NatAssign.Instruction.value,Parts.literal]
  · exact unsignedFinished_output N v source

theorem corrected_precision (N : ℕ) (v : ℕ→Parts) (source : ℕ) : corrected N v source 640=N := by
  unfold corrected
  split_ifs
  · simpa [GlueMachine.writeZero,NatAssign.values,NatAssign.Instruction.update,
      NatAssign.Instruction.target,NatAssign.Instruction.value] using unsignedFinished_precision N v source
  · exact unsignedFinished_precision N v source

theorem corrected_counter (N : ℕ) (v : ℕ→Parts) (source : ℕ) : corrected N v source 641=0 := by
  unfold corrected
  split_ifs <;> simp [GlueMachine.writeZero,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,NatAssign.Instruction.value,unsignedFinished]

theorem corrected_outside (N : ℕ) (v : ℕ→Parts) (source i : ℕ)
    (hi : i∉GlueMachine.Runtime.ids) : corrected N v source i=dataValues v i := by
  have h602 : i≠602 := by intro h;subst i;exact hi (by decide)
  have h603 : i≠603 := by intro h;subst i;exact hi (by decide)
  have h604 : i≠604 := by intro h;subst i;exact hi (by decide)
  have h641 : i≠641 := by intro h;subst i;exact hi (by decide)
  unfold corrected
  split_ifs <;> simp only [GlueMachine.writeZero,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,NatAssign.Instruction.value,unsignedFinished,returned,
    Function.update_of_ne h602,Function.update_of_ne h603,Function.update_of_ne h604,
    Function.update_of_ne h641,ite_eq_right hi]

theorem copyOutput_values (target : ℕ) (v : ℕ→ℕ) :
    NatAssign.values (copyOutput target) v=writeParts v target ⟨v 602,v 603,v 604⟩ := by
  have hp := positivePort_ge target
  have hn := negativePort_ge target
  simp (disch := omega) [copyOutput,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,NatAssign.Instruction.value,writeParts]

theorem finishCall_values (N : ℕ) (v : ℕ→Parts) (target source : ℕ) :
    NatAssign.values (finishCall target) (corrected N v source)=
      initialValues N (Function.update v target (result N (v source))) := by
  rw [finishCall,values_append,copyOutput_values,corrected_output]
  have hp := positivePort_ge target
  have hn := negativePort_ge target
  have hd := denominatorPort_ge target
  ext i
  simp only [NatAssign.clearList_values,privateTapes_mem,initialValues]
  by_cases h640 : i=640
  · subst i
    simp (disch := omega) [writeParts,corrected_precision]
  by_cases h641 : i=641
  · subst i
    simp (disch := omega) [writeParts,corrected_counter,dataValues_small]
  by_cases hi : i∈GlueMachine.Runtime.ids
  · have hsmall := ids_small i hi
    simp (disch := omega) [hi,h640,h641,dataValues_small _ hsmall]
  · simp only [hi,false_and,ite_false,Function.update_of_ne h640]
    rw [←writeParts_dataValues]
    simp only [writeParts,Function.update_apply]
    split_ifs <;> first | rfl | exact corrected_outside N v source i hi

theorem unsignedFinished_width (S : Finset ℕ) (N : ℕ) (v : ℕ→Parts) (source W : ℕ)
    (hs : source∈S) (hw : WidthBank S W v) (hN : N.bits.length≤W) (hW : 4≤W)
    (i : ℕ) (hi : i∈allIds S) : (unsignedFinished N v source i).bits.length≤workWidth N W := by
  by_cases h641 : i=641
  · subst i;simp [unsignedFinished,workWidth]
  · simp only [unsignedFinished,Function.update_of_ne h641,returned]
    split_ifs with hp
    · have hm : (Phase.magnitude (v source)).bits.length≤W+1 :=
        (IntegerNormSquare.magnitude_bits_length_le _ _).trans
          (Nat.add_le_add_right (max_le (hw source hs).1 (hw source hs).2.1) 1)
      exact (core_width _ _ N (W+1) hm ((hw source hs).2.2.trans (by omega))
        (hN.trans (by omega)) (by omega) i hp).trans (by
          unfold workWidth
          simpa only [Nat.add_assoc] using Nat.mul_le_mul_right ((N+W+9)^4) (show 2^30≤2^32 by norm_num))
    · have hr := (Finset.mem_union.mp hi).resolve_right hp
      exact (dataValues_width S v W hw i hr).trans (by
        have h : N+W+9≤(N+W+9)^4 := Nat.le_self_pow (by decide) _
        unfold workWidth;omega)

theorem corrected_width (S : Finset ℕ) (N : ℕ) (v : ℕ→Parts) (source W : ℕ)
    (hs : source∈S) (hw : WidthBank S W v) (hN : N.bits.length≤W) (hW : 4≤W)
    (i : ℕ) (hi : i∈allIds S) : (corrected N v source i).bits.length≤workWidth N W := by
  unfold corrected
  split_ifs
  · have h1 : (1:ℕ).bits.length≤workWidth N W := by
      have h : 1≤(N+W+9)^4 := one_le_pow₀ (by omega)
      simp only [show (1:ℕ).bits.length=1 from rfl];unfold workWidth;omega
    simp only [GlueMachine.writeZero,NatAssign.values,NatAssign.Instruction.update,
      NatAssign.Instruction.target,NatAssign.Instruction.value,Function.update_apply]
    split_ifs <;> first | exact h1 | exact unsignedFinished_width S N v source W hs hw hN hW i hi | simp
  · exact unsignedFinished_width S N v source W hs hw hN hW i hi

theorem core_protects_sign : Core.protectsRegister 200=true := by rfl

#print axioms finishCall_values
#print axioms corrected_width
end Maxwell.Continuum.RationalDataflow.Glue
