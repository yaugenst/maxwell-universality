import Maxwell.Continuum.CalibrationRootContext

/-! Exact actual output of the indexed real or imaginary root coefficient. -/
namespace Maxwell.Continuum.RationalDataflow.RootTable
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

def scalar (grid : ℕ) [NeZero grid] (scale : ℚ) (N index : ℕ) : ℚ :=
  if index%2=0 then
    (Calibration.rationalRootCoefficient grid scale N (RootFrequency.frequency grid index)).re.center
  else (Calibration.rationalRootCoefficient grid scale N (RootFrequency.frequency grid index)).im.center

def entryWidth (grid N B I : ℕ) : ℕ :=
  RootComponent.width (RootGrid.coefficientRawWidth grid N (RootIndexed.decodedWidth B) I)
def emitCode : Code := .seq RootIndexed.code
  (.seq RootComponent.control.code (PartArray.writeAtCode 201 12))
def emitCost (grid N B I W : ℕ) : ℕ := RootIndexed.costBound grid N B I+
  (3*operationCost (entryWidth grid N B I)+1)+2^20*(W+5)^2

structure Emitted {T : ℕ} (a : PartArray.Table T) (target : Fin T) (S : Finset ℕ)
    (grid N B I : ℕ) [NeZero grid] (scale : Parts) (s : Store) where
  parts : ℕ→Parts
  naturals : ℕ→ℕ
  entry : Parts
  context : Context S N naturals parts s
  good : Good S parts
  width : WidthBank S (entryWidth grid N B I) parts
  natural_width : ∀i∈RootFrequency.ids,
    (naturals i).bits.length≤returnWidth grid (RootIndexed.decodedWidth B)
  grid_eq : naturals 331=grid
  work_zero : ∀i∈NaturalQuotient.workPorts,naturals i=0
  scale_eq : parts 9=scale
  entry_eq : entry=parts 12
  value : entry.value=scalar grid scale.value N target.val
  output_table : (a.set target entry).OutputReady s

theorem emit_executes {T : ℕ} (a : PartArray.Table T) (target : Fin T)
    (S : Finset ℕ) (hS : RootGrid.coefficientInputs⊆S) (h8 : 8∈S)
    (grid degree N B I W : ℕ) [NeZero grid] (hgrid : grid=2*degree+1) (hB : 2≤B) (hI : 1≤I)
    (n : ℕ→ℕ) (initial : ℕ→Parts) (hn331 : n 331=grid) (hn330 : n 330=target.val)
    (hn : ∀i∈RootFrequency.ids,(n i).bits.length≤B)
    (hz : ∀i∈NaturalQuotient.workPorts,n i=0)
    (hw : WidthBank S I initial) (hg : Good S initial)
    (hm : a.MetadataWidth W) (hfit : entryWidth grid N B I≤addressValue a.width) (hsep : a.Separated)
    (index : List Bool) (hindex : addressValue index=target.val) (hlen : index.length≤W)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hctx : Context S N n initial s) (ha : a.OutputReady s) (hi : BankArray.Word s.val 201 index) :
    ∃ (cost : ℕ) (t : Store) (out : Emitted a target S grid N B I (initial 9) t),
      Executes input tape emitCode cost s t ∧ cost≤emitCost grid N B I W ∧
      t.val.memory=a.writeMemory target out.entry s.val.memory ∧
      t.val.tapes 201=s.val.tapes 201 ∧ t.val.output=s.val.output := by
  obtain ⟨c0,s0,e0,h0,⟨state⟩,z0,f0⟩ := RootIndexed.executes S hS h8 grid degree N B I
    hgrid hB hI n initial hn331 hn hz hw hg input tape s hctx.natural hctx.rational
    hctx.scratch hctx.glue hctx.phase hctx.glue_precision hctx.phase_range hctx.phase_precision
  have ctx0 := coefficient_context state z0
  have a0 := RootGrid.coefficient_outputReady a ha f0 state.rational_bank
  have i0 := BankArray.word_of_eq (f0.tapes 201 (RootGrid.coefficient_protected S 201 (by simp))) hi
  have hcomp : RootComponent.inputs⊆S := by
    intro i hi
    simp only [RootComponent.inputs,Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl|rfl|rfl|rfl
    · exact h8
    all_goals exact hS (by decide)
  have hwpos : 1≤RootGrid.coefficientRawWidth grid N (RootIndexed.decodedWidth B) I := by
    unfold RootGrid.coefficientRawWidth
    omega
  obtain ⟨c1,s1,e1,h1,r1,g1,w1,f1⟩ := RootComponent.executes S hcomp state.parts
    (RootGrid.coefficientRawWidth grid N (RootIndexed.decodedWidth B) I) hwpos state.width state.good
    input tape s0 state.rational_bank
  have ctx1 := ctx0.arithmetic_frame f1 r1
  have f1' : BinaryPrecision.Frame (RootGrid.coefficientWorkspace S) s0.val s1.val :=
    f1.mono ((Finset.subset_union_right : workspace S⊆RootGrid.startWorkspace S).trans
    Finset.subset_union_left)
  have a1 := RootGrid.coefficient_outputReady a a0 f1' r1
  have i1 := BankArray.word_of_eq (f1'.tapes 201 (RootGrid.coefficient_protected S 201 (by simp))) i0
  have heS : 12∈S := hS (by decide)
  have wf := (w1 12 heS).mono hfit
  have pos : 0<addressValue a.width := by
    have hpos : 0<entryWidth grid N B I := by unfold entryWidth RootComponent.width;omega
    omega
  obtain ⟨c2,t,e2,h2,r2,a2,m2,f2⟩ := PartArray.writeAt_executes a S 201 (by decide) 12 heS
    (RootComponent.values state.parts) target pos wf hsep input tape index hindex s1 r1 a1 i1
  have parity : (state.parts 8).value=(target.val%2:ℕ) := by
    rw [state.external 8 (by decide) (by decide) (by decide) (by decide)]
    simp only [RootFrequency.parityParts,Function.update_self,RootFrequency.parity_value,hn330]
  have scale0 : RootFrequency.parityParts n initial 9=initial 9 := by
    simp only [RootFrequency.parityParts,Function.update_of_ne (by decide : (9:ℕ)≠8)]
  let out : Emitted a target S grid N B I (initial 9) t := {
    parts := RootComponent.values state.parts
    naturals := RootGrid.completeNaturals state
    entry := RootComponent.values state.parts 12
    context := ctx1.write_frame f2 r2
    good := g1
    width := w1
    natural_width := complete_width state
    grid_eq := complete_grid state
    work_zero := complete_zero state
    scale_eq := by
      rw [RootComponent.other _ 9 (by decide),state.external 9 (by decide) (by decide) (by decide) (by decide)]
      exact scale0
    entry_eq := rfl
    value := by
      rw [RootComponent.selected_parity state.parts target.val parity
        (state.good 10 (hS (by decide))) (state.good 11 (hS (by decide))),state.real_value,state.imag_value,
        scale0,hn330]
      rfl
    output_table := a2 }
  refine ⟨c0+(c1+c2),t,out,e0.seq (e1.seq e2),?_,?_,?_,?_⟩
  · change c2≤a.writeCost index (RootComponent.values state.parts 12) at h2
    have hwrite := a.writeCost_bound W hm index hlen (RootComponent.values state.parts 12)
    change c1≤3*operationCost (entryWidth grid N B I)+1 at h1
    unfold emitCost
    omega
  · change t.val.memory=a.writeMemory target (RootComponent.values state.parts 12) s.val.memory
    rw [m2,f1.memory,f0.memory]
  · exact (f2.2.2.2.1 201 (Or.inr (by decide)) (by decide)).trans
      ((f1'.tapes 201 (RootGrid.coefficient_protected S 201 (by simp))).trans
        (f0.tapes 201 (RootGrid.coefficient_protected S 201 (by simp))))
  · exact f2.2.2.1.trans (f1.output.trans f0.output)

#print axioms emit_executes
end Maxwell.Continuum.RationalDataflow.RootTable
