import Maxwell.Continuum.CalibrationRootGridLoopState
import Maxwell.Continuum.CalibrationRootGridCost

/-! The countdown body discharges its own semantic and width invariant
by executing the actual sample program and exact rational additions. -/
namespace Maxwell.Continuum.RationalDataflow.RootGrid
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

theorem LoopState.step_executes {S : Finset ℕ} {grid N : ℕ} [NeZero grid]
    {frequency : Fin 3→ℤ} {B I : ℕ} {initial : ℕ→Parts} {remaining : ℕ}
    (hS : sumInputs⊆S) (hw : WidthBank S I initial) (hsize : (grid^3).bits.length≤B)
    (xs : List Bool) (hxs : addressValue xs=remaining)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (h : LoopState S grid N frequency B I initial (remaining+1) s)
    (hword : BankArray.Word s.val 342 xs) :
    ∃cost t,Executes input tape stepCode cost s t ∧
      Nonempty (LoopState S grid N frequency B I initial remaining t) ∧
      cost≤2^3074*(N+loopWidth grid N B I 0+xs.length+20)^56 ∧
      BinaryPrecision.Frame (sampleWorkspace S) s.val t.val := by
  have hr : remaining<grid^3 := by have := h.remaining_le;omega
  have hidx := (RationalWords.bits_mono hr.le).trans hsize
  have hbd : B≤dataWidth B I := by unfold dataWidth naturalWidth;omega
  have hnat : ∀i∈ids,(h.naturals i).bits.length≤dataWidth B I := fun i hi =>
    (h.facts.all_width i hi).trans (by unfold dataWidth;omega)
  have h9 : h.parts 9=initial 9 := h.external 9 (by omega) (by decide) (by decide)
  have w9 : (h.parts 9).Width (dataWidth B I) := by
    rw [h9]
    exact (hw 9 (hS (by decide))).mono (by unfold dataWidth;omega)
  have hpos : 0<h.naturals 331 := by
    rw [h.facts.grid_eq]
    exact Nat.pos_of_ne_zero (NeZero.ne grid)
  have hwidth := loopWidth_ge grid N B I (remaining+1)
  have hxW : (addressValue xs).bits.length≤dataWidth B I := by rw [hxs];exact hidx.trans hbd
  obtain ⟨c,t,e,hc,r,g,w,nb,z,gl,ph,wp,wq,wn,f⟩ := RootGrid.step_executes S hS N (dataWidth B I)
    (loopWidth grid N B I (remaining+1)) h.naturals h.parts hwidth.2.2.1 hwidth.1 hwidth.2.1
    hnat h.width h.good w9 hwidth.2.2.2 h.facts.work_zero hpos xs hxW input tape s
    h.rational_bank h.natural_bank h.scratch h.glue h.phase h.precision_glue h.phase_range
    h.precision_phase hword
  simp only [hxs] at r g w nb
  have w' : WidthBank S (loopWidth grid N B I remaining)
      (accumulated N (indexedInputs h.naturals remaining) h.parts) := by
    change WidthBank S (loopWidth grid N B I (remaining+1)+summandWidth N B I+1) _ at w
    rw [loopWidth_step grid N B I remaining hr] at w
    exact w
  have hspos : 0 < indexedInputs h.naturals remaining 331 := by
    simpa only [indexedInputs,Function.update_of_ne (by decide : (331:ℕ)≠330)] using hpos
  have hgSample := sampleParts_good S (Finset.subset_union_left.trans hS) N
    (indexedInputs h.naturals remaining) h.parts h.good hspos
  have hacc := accumulated_values S hS N (indexedInputs h.naturals remaining) h.parts hgSample
  have hsample := h.facts.indexed_exact N remaining h.parts (h.good 9 (hS (by decide)))
  have hre : (sampleParts N (indexedInputs h.naturals remaining) h.parts 6).value=
      realSummand grid N frequency initial remaining := by
    simpa only [realSummand,h9] using hsample.1
  have him : (sampleParts N (indexedInputs h.naturals remaining) h.parts 7).value=
      imagSummand grid N frequency initial remaining := by
    simpa only [imagSummand,h9] using hsample.2
  have result : LoopState S grid N frequency B I initial remaining t := {
    naturals := values (indexedInputs h.naturals remaining)
    parts := accumulated N (indexedInputs h.naturals remaining) h.parts
    remaining_le := hr.le
    facts := h.facts.next remaining hidx
    natural_bank := nb
    rational_bank := r
    good := g
    width := w'
    external := fun i hi h10 h11 =>
      (accumulated_other N _ _ i ⟨hi,h10,h11⟩).trans (h.external i hi h10 h11)
    real_value := by
      rw [hacc.1,h.real_value,hre,tailSum_step _ _ _ hr]
      ring
    imag_value := by
      rw [hacc.2,h.imag_value,him,tailSum_step _ _ _ hr]
      ring
    scratch := z
    glue := gl
    phase := ph
    precision_glue := wp
    phase_range := wq
    precision_phase := wn }
  refine ⟨c,t,e,⟨result⟩,?_,f⟩
  apply (hc.trans (stepCost_polynomial _ _ _ _ hwidth.2.2.2)).trans
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
    (by have := loopWidth_le_final grid N B I (remaining+1);omega) 56)

#print axioms LoopState.step_executes
end Maxwell.Continuum.RationalDataflow.RootGrid
