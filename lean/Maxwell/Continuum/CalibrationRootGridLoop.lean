import Maxwell.Continuum.CalibrationRootGridLoopStep

/-! Full product-grid quadrature by one fixed runtime countdown program.
The body invariant and all intermediate widths are proved internally. -/
namespace Maxwell.Continuum.RationalDataflow.RootGrid
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
attribute [local irreducible] stepCode

def sumCode : Code := countedProgram 342 stepCode
def sumWorkspace (S : Finset ℕ) : Finset ℕ := {342}∪sampleWorkspace S
def sumCost (grid N B I length : ℕ) : ℕ :=
  (grid^3+1)*(13*length+15)+grid^3*(2^3074*(N+loopWidth grid N B I 0+length+20)^56)

theorem counter_binary_frame {s t : Store} (f : CountedShifted.Frame 342 s t) :
    BinaryPrecision.Frame {342} s.val t.val := by
  refine ⟨f.1,f.2.1,f.2.2.1,f.2.2.2.1,f.2.2.2.2.1,?_⟩
  intro i hi
  exact f.2.2.2.2.2.1 i (by simpa only [Finset.mem_singleton] using hi)

theorem sum_executes (S : Finset ℕ) (hS : sumInputs⊆S)
    (grid N : ℕ) [NeZero grid] (frequency : Fin 3→ℤ) (B I : ℕ)
    (n : ℕ→ℕ) (initial : ℕ→Parts) (hfacts : InputFacts grid frequency B n)
    (hw : WidthBank S I initial) (hg : Good S initial) (hsize : (grid^3).bits.length≤B)
    (xs : List Bool) (origin : ℤ) (hxs : addressValue xs=grid^3)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : Ready S initial s) (hb : NatAssign.Bank ids n s.val) (hz : ∀i,i<5 → Blank s.val i)
    (hglue : Glue.Clean s.val) (hphase : Phase.Runtime.Clean s.val)
    (hp : Word s.val 640 N) (hq : Word s.val 652 1) (hprec : Word s.val 653 N)
    (hword : s.val.tapes 342=BitTape.shifted xs origin) :
    ∃cost t finalWord,Executes input tape sumCode cost s t ∧
      Nonempty (LoopState S grid N frequency B I initial 0 t) ∧
      t.val.tapes 342=BitTape.shifted finalWord origin ∧ finalWord.length=xs.length ∧
      cost≤sumCost grid N B I xs.length ∧
      BinaryPrecision.Frame (sumWorkspace S) s.val t.val := by
  let inv : ℕ→Store→Prop := fun remaining st =>
    Nonempty (LoopState S grid N frequency B I initial remaining st) ∧
      BinaryPrecision.Frame (sumWorkspace S) s.val st.val
  let bound : ℕ→ℕ := fun _ => 2^3074*(N+loopWidth grid N B I 0+xs.length+20)^56
  have stable : ∀remaining a b,CountedShifted.Frame 342 a b → inv remaining a → inv remaining b := by
    intro remaining a b f hh
    rcases hh.1 with ⟨state⟩
    exact ⟨⟨state.count_frame f⟩,hh.2.trans ((counter_binary_frame f).mono Finset.subset_union_left)⟩
  have bodyCorrect : ∀remaining ys a,inv (remaining+1) a →
      a.val.tapes 342=BitTape.shifted ys origin → addressValue ys=remaining → ys.length=xs.length →
      ∃cost b,Executes input tape stepCode cost a b ∧ inv remaining b ∧
        b.val.tapes 342=BitTape.shifted ys origin ∧ cost≤bound remaining := by
    intro remaining ys a hh hword hvalue hlen
    rcases hh.1 with ⟨state⟩
    obtain ⟨c,b,e,hstate,hc,f⟩ := state.step_executes hS hw hsize ys hvalue input tape a ⟨origin,hword⟩
    refine ⟨c,b,e,⟨hstate,hh.2.trans (f.mono Finset.subset_union_right)⟩,
      (f.tapes 342 (counter_outside S)).trans hword,?_⟩
    simpa only [bound,hlen] using hc
  have initialState : LoopState S grid N frequency B I initial (grid^3) s := {
    naturals := n
    parts := initial
    remaining_le := le_rfl
    facts := hfacts
    natural_bank := hb
    rational_bank := hs
    good := hg
    width := hw.mono (by unfold loopWidth initialWidth dataWidth;omega)
    external := fun _ _ _ _ => rfl
    real_value := by rw [tailSum_initial,add_zero]
    imag_value := by rw [tailSum_initial,add_zero]
    scratch := hz
    glue := hglue
    phase := hphase
    precision_glue := hp
    phase_range := hq
    precision_phase := hprec }
  obtain ⟨c,t,finalWord,e,hInv,hword',hlen,_,hc⟩ := counted_executes_sized 342 origin stepCode
    input tape xs.length inv bound stable bodyCorrect (grid^3) xs s hxs hword rfl
    ⟨⟨initialState⟩,BinaryPrecision.Frame.refl _ _⟩
  refine ⟨c,t,finalWord,e,hInv.1,hword',hlen,?_,hInv.2⟩
  simpa only [bound,sumCost,Finset.sum_const,Finset.card_range,smul_eq_mul] using hc

theorem LoopState.final_values {S : Finset ℕ} {grid N : ℕ} [NeZero grid]
    {frequency : Fin 3→ℤ} {B I : ℕ} {initial : ℕ→Parts} {s : Store}
    (h : LoopState S grid N frequency B I initial 0 s) :
    (h.parts 10).value=(initial 10).value+
      ∑j,(Calibration.rootProductSample grid (initial 9).value N frequency j).re.center ∧
    (h.parts 11).value=(initial 11).value+
      ∑j,(Calibration.rootProductSample grid (initial 9).value N frequency j).im.center := by
  constructor
  · rw [h.real_value]
    exact congrArg ((initial 10).value+·) (tailSum_product_grid grid
      (fun j => (Calibration.rootProductSample grid (initial 9).value N frequency j).re.center))
  · rw [h.imag_value]
    exact congrArg ((initial 11).value+·) (tailSum_product_grid grid
      (fun j => (Calibration.rootProductSample grid (initial 9).value N frequency j).im.center))

#print axioms sum_executes
#print axioms LoopState.final_values
end Maxwell.Continuum.RationalDataflow.RootGrid
