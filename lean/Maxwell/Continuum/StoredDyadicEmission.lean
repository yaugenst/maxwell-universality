import Maxwell.Continuum.StoredIntegerEmission
import Maxwell.Continuum.DyadicFloorStoredPowerCost
import Maxwell.Continuum.DyadicFloorOutputWidth
import Maxwell.Continuum.DyadicFloorFrame
import Maxwell.Continuum.RationalDataflowIntegerCanonical

/-! A raw rational register representing a dyadic is converted by actual
stored-scale division and signed normalization, then its integer numerator
is emitted. The fixed program contains neither precision nor output words. -/
namespace Maxwell.Continuum.RationalDataflow.StoredDyadic
open Maxwell.Cost Maxwell.Cost.Structured
open RationalAccumulator (Word Blank)
open StoredInteger (slots ready_emit_frame canonical_abs_width)
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

theorem round_value {P : ℕ} (d : Dyadic P) : roundDyadic P d.value=d := by
  have he : d.value*(2:ℚ)^P=(d.numerator:ℚ) := by
    unfold Dyadic.value
    exact div_mul_cancel₀ _ (pow_ne_zero _ (by norm_num))
  unfold roundDyadic
  rw [he,Int.floor_intCast]

def code : Code := .seq (DyadicFloor.StoredPower.code 0 0)
  (.seq (IntegerCanonical.code 0 0) (IntegerEmit.code 0))

def outputValues {P : ℕ} (d : Dyadic P) (v : ℕ→Parts) : ℕ→Parts :=
  Function.update v 0 (Parts.literal (d.numerator:ℚ))

theorem executes {P : ℕ} (d : Dyadic P) (v : ℕ→Parts) (B : ℕ)
    (hv : WidthBank slots B v) (hx : (v 0).Valid) (hvalue : (v 0).value=d.value)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hr : Ready slots v s) (hclean : DyadicFloor.Clean s.val) (hpower : Word s.val 144 (2^P)) :
    ∃cost t,Executes input tape code cost s t ∧ cost≤2^145*(P+B+6)^2 ∧
      Ready slots (outputValues d v) t ∧ WidthBank slots (2*B+P+3) (outputValues d v) ∧
      DyadicFloor.Clean t.val ∧ Word t.val 144 (2^P) ∧
      t.val.output=(Codec.int d.numerator).reverse++s.val.output ∧
      t.val.memory=s.val.memory ∧
      (∀k,k∉DyadicFloor.StoredPower.workspace slots → t.val.tapes k=s.val.tapes k) := by
  obtain ⟨c0,s0,e0,hc0,r0,z0,p0,f0⟩ := DyadicFloor.StoredPower.executes slots P 0 0
    (by decide) (by decide) v B hv hx input tape s hr hclean hpower
  let v0 := Function.update v 0 (DyadicFloor.result P (v 0))
  have w0 : WidthBank slots (2*B+P+2) v0 := by
    intro i hi
    have he : i=0 := by simpa only [slots,Finset.mem_singleton] using hi
    subst i
    exact DyadicFloor.result_raw_width P B (v 0) (hv 0 (by decide))
  obtain ⟨c1,s1,e1,hc1,r1,f1⟩ := IntegerCanonical.executes slots 0 0 (by decide) (by decide)
    v0 (2*B+P+2) w0 input tape s0 r0
  have he : IntegerCanonical.result (v0 0)=Parts.literal (d.numerator:ℚ) := by
    rw [show v0 0=DyadicFloor.result P (v 0) from Function.update_self ..]
    rw [IntegerCanonical.result_eq_literal_value _ rfl,DyadicFloor.result_value P (v 0) hx,hvalue,round_value]
  have hvalues : Function.update v0 0 (IntegerCanonical.result (v0 0))=outputValues d v := by
    rw [he]
    exact Function.update_idem ..
  rw [hvalues] at r1
  have w1 : WidthBank slots (2*B+P+3) (outputValues d v) := by
    intro i hi
    have hi0 : i=0 := by simpa only [slots,Finset.mem_singleton] using hi
    subst i
    have hh := IntegerCanonical.result_width (2*B+P+2) (v0 0) (w0 0 (by decide))
    simpa only [he,outputValues,Function.update_self,Nat.add_assoc] using hh
  have hp : Word s1.val (positivePort 0) d.numerator.toNat := by
    have hh := r1.1 (positivePort 0) (cell_mem (by decide : 0∈slots) (by simp [cellPorts]))
    simpa [dataValues_positive,outputValues,Parts.literal] using hh
  have hn : Word s1.val (negativePort 0) (-d.numerator).toNat := by
    have hh := r1.1 (negativePort 0) (cell_mem (by decide : 0∈slots) (by simp [cellPorts]))
    simpa [dataValues_negative,outputValues,Parts.literal] using hh
  obtain ⟨t,e2,out2,f2⟩ := IntegerEmit.executes 0 d.numerator input tape s1 hp hn
  have clean1 := z0.arithmetic_frame f1
  have power1 := RationalAccumulator.word_of_eq
    (f1.tapes 144 (outside_workspace slots 144 (by decide))) p0
  have hwout := canonical_abs_width d.numerator (2*B+P+3) (w1 0 (by decide))
  refine ⟨c0+(c1+(20*d.numerator.natAbs.bits.length+30)),t,e0.seq (e1.seq e2),?_,
    ready_emit_frame r1 f2,w1,?_,RationalAccumulator.word_of_eq (congrFun f2.2.2.2.2 144) power1,
    ?_,f2.2.2.1.trans (f1.memory.trans f0.memory),?_⟩
  · have hc0' := hc0.trans (DyadicFloor.costBound_polynomial P B)
    unfold operationCost at hc1
    nlinarith only [hc0',hc1,hwout,Nat.zero_le P,Nat.zero_le B]
  · exact ⟨RationalAccumulator.blank_of_eq (congrFun f2.2.2.2.2 4) clean1.1,
      fun i hi=>RationalAccumulator.blank_of_eq (congrFun f2.2.2.2.2 i) (clean1.2 i hi)⟩
  · simpa only [f1.output,f0.output] using out2
  · intro k hk
    have ho : k∉RationalDataflow.workspace slots := by
      intro hm
      apply hk
      exact Finset.mem_insert_of_mem (by
        rcases Finset.mem_union.mp hm with hz|hi
        · exact Finset.mem_union_left _ (by simp only [Finset.mem_insert,Finset.mem_singleton] at hz ⊢;tauto)
        · exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_union_left _ hi)))
    exact (congrFun f2.2.2.2.2 k).trans ((f1.tapes k ho).trans (f0.tapes k hk))

#print axioms executes
end Maxwell.Continuum.RationalDataflow.StoredDyadic
