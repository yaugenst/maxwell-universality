import Maxwell.Continuum.ParameterSourceFrontEnd
import Maxwell.Continuum.ParameterSourceOuterMachine
import Maxwell.Continuum.ParameterSourceResources
import Maxwell.Source.Nonzero

/-! The source bytes drive geometry construction and the complete parameter
search. Retained source and geometry data share the same memory throughout. -/
noncomputable section
namespace Maxwell.Continuum.Parameters.SourceSelected
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RoutingPorts.Complete
open Maxwell.Composition
open RationalAccumulator (Word Blank)
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

def code (κ η e : ℕ) : Code := .seq (SourceFrontEnd.code κ η e) SourceOuter.code
def retainedWork : Finset ℕ := SourcePrepare.work∪SourceOuter.work

structure Result (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz)
    (hn : 0<S.n) (hm2 : 2≤S.nnz) (e : ℕ) (s : Store) : Prop where
  parameters : ∃v,
    (∀i∈OuterMachine.ids,Word s.val (SourceOuter.relocation i) (v i)) ∧
    (∀i∈OuterMachine.ids,(v i).bits.length≤SourceOuter.outputWidth p S hm hn hm2 e) ∧
    OuterMachine.StageOutputs (SourceOuter.data p S hm e) (SourceOuter.data_positive p S hm e)
      e (SourceOuter.exponent p S hm e) v
  scratch : NatAssign.Scratch s.val
  logWord : Word s.val 2200 (inputLog S.nnz)
  saved : ∃previous : Store,
    CountedGeometry.Result S (SelectedInput.input p S hm).precision previous ∧
    BinaryPrecision.Frame retainedWork previous.val s.val
  inputHead : s.val.inputHead=(Codec.source S).length
  randomCursor : s.val.randomCursor=0
  output : s.val.output=[]

theorem executes (p : Source.Parameters) (S : Source.SparseSystem) (hp : Source.Promises p S)
    (hm : 2≤S.nnz) (hb : S.source≠0) (e : ℕ) (tape : ℕ→Bool) :
    let positive : 0<S.nnz:=by omega
    let dimension : 0<S.n:=Source.dimension_pos_of_source_ne_zero S hb
    let precision:=(SelectedInput.input p S positive).precision
    ∃room : SourceGraph.Positive.dimension S precision<2^SourceGraph.Positive.width S precision,
      ∃steps t,Executes (Codec.source S) tape (code ⌈p.conditionExponent⌉₊ ⌈p.accuracyExponent⌉₊ e)
          steps (Store.ofState BitRAMState.initial) t ∧
        steps≤SourceGraph.Incidence.totalBudget p S ⌈p.conditionExponent⌉₊ ⌈p.accuracyExponent⌉₊+
          SourceExecution.cost ⌈p.conditionExponent⌉₊ ⌈p.accuracyExponent⌉₊ e S precision room+
          SourceOuter.cost p S positive dimension hm e ∧
        Result p S positive dimension hm e t := by
  dsimp only
  obtain ⟨room,c₀,a,e₀,h₀,ha,hi,hr,ho⟩:=SourceFrontEnd.executes p S hp hm hb e tape
  obtain ⟨c₁,t,v,e₁,h₁,bt,zt,wt,outputs,frame,log⟩:=SourceOuter.executes p S (by omega)
    (Source.dimension_pos_of_source_ne_zero S hb) hm e (Codec.source S) tape a ha
  obtain ⟨previous,geometry,prepareFrame⟩:=ha.saved
  exact ⟨room,c₀+c₁,t,e₀.seq e₁,Nat.add_le_add h₀ h₁,
    ⟨⟨v,bt,wt,outputs⟩,zt,log,⟨previous,geometry,
      (prepareFrame.mono Finset.subset_union_left).trans (frame.mono Finset.subset_union_right)⟩,
      frame.inputHead.trans hi,frame.randomCursor.trans hr,frame.output.trans ho⟩⟩

theorem retainedWork_disjoint : Disjoint (Finset.Icc 5 1260) retainedWork := by
  apply Finset.disjoint_left.mpr
  intro i hi member
  have bounds:=Finset.mem_Icc.mp hi
  rcases Finset.mem_union.mp member with first|second
  · have separate : ∀j∈SourcePrepare.work,j<5 ∨ 1260<j := by decide +kernel
    have := separate i first
    omega
  · obtain ⟨j,hj,eq⟩:=Finset.mem_image.mp second
    have upper : ∀j∈OuterMachine.workspace,j<2300 := by decide +kernel
    have := upper j hj
    change TapeBlockSwap.index 4 1257 3000 j=i at eq
    simp only [TapeBlockSwap.index] at eq
    split_ifs at eq <;> omega

theorem Result.data {p : Source.Parameters} {S : Source.SparseSystem} {hm : 0<S.nnz}
    {hn : 0<S.n} {hm2 : 2≤S.nnz} {e : ℕ} {s : Store} (h : Result p S hm hn hm2 e s) :
    SourceGraph.Retain.Data S (SelectedInput.input p S hm).precision s.val := by
  obtain ⟨previous,geometry,frame⟩:=h.saved
  apply geometry.data.transport
  intro i lo hi
  apply frame.tapes
  exact Finset.disjoint_left.mp retainedWork_disjoint (Finset.mem_Icc.mpr ⟨by omega,by omega⟩)

theorem exponent_eq_sourceStage (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz) :
    SourceOuter.exponent p S hm MasterConstants.exponent=sourceStage p S hm := rfl

#print axioms executes
#print axioms Result.data
end Maxwell.Continuum.Parameters.SourceSelected
