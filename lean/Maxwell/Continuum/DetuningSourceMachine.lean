import Maxwell.Continuum.DetuningDrawMachine
import Maxwell.Continuum.ParameterSourceSelectedFrame
import Maxwell.Continuum.ContinuumRandomProgram

/-! The actual source-selected operands determine the finite fair draw.
The output numerator and precision are the exact physical dyadic midpoint. -/
noncomputable section
namespace Maxwell.Continuum.DetuningMachine
open Maxwell.Cost Maxwell.Cost.Structured
open RationalAccumulator (Word Blank)
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
attribute [local irreducible] MasterConstants.exponent Parameters.sourceInput
  RealizationParameters.randomDraw

def initial (v : ℕ→ℕ) (i : ℕ) : ℕ := if i∈localIds then 0 else v i
def sourceCode : Code := .seq countCode drawCode
def sourceCost (n B : ℕ) : ℕ := countCost B+drawCost n (countWidth B)

theorem outer_source_size (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz)
    (e : ℕ) (v : ℕ→ℕ)
    (h : Parameters.OuterMachine.dataOf v=Parameters.SourceOuter.data p S hm e) :
    v 2211=S.nnz := congrArg Parameters.OuterMachine.Data.sourceSize h

theorem source_fields (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz)
    (v : ℕ→ℕ)
    (h : Parameters.OuterMachine.StageOutputs (Parameters.SourceOuter.data p S hm MasterConstants.exponent)
      (Parameters.SourceOuter.data_positive p S hm MasterConstants.exponent) MasterConstants.exponent
      (Parameters.SourceOuter.exponent p S hm MasterConstants.exponent) v) :
    initial v 2211=S.nnz ∧ initial v 2245=RealizationParameters.count p S hm ∧
    initial v 2237=2^Parameters.tauBits (RealizationParameters.length p S hm)
      (RealizationParameters.spacing p S hm) (RealizationParameters.length_pos p S hm) := by
  have kept (i : ℕ) (hi : i<4500) : initial v i=v i := by simp [initial,localIds];omega
  refine ⟨(kept 2211 (by decide)).trans (outer_source_size p S hm _ v h.core.data),?_,?_⟩
  · rw [kept 2245 (by decide),h.buffer.box,Parameters.SourceOuter.data_input]
    rfl
  · rw [kept 2237 (by decide),h.tau.denominator,Parameters.OuterMachine.Data.detuningDen,
      Parameters.SourceOuter.data_input]
    rw [Parameters.tauBits,Parameters.OuterTau.precision_eq _ _ (RealizationParameters.length_pos p S hm)]
    rfl

theorem source_executes (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz)
    (hn : 0<S.n) (hm2 : 2≤S.nnz) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (selected : Parameters.SourceSelected.Result p S hm hn hm2 MasterConstants.exponent s) :
    let n := RealizationParameters.randomBitCount p S hm
    let j := RealizationParameters.randomDraw p S hm (fun i=>tape (s.val.randomCursor+i.val))
    let B := Parameters.SourceOuter.outputWidth p S hm hn hm2 MasterConstants.exponent
    ∃cost t w,Executes input tape sourceCode cost s t ∧ cost≤sourceCost n B ∧
      NatAssign.Bank ids w t.val ∧ NatAssign.Scratch t.val ∧
      (∀i∈ids,(w i).bits.length≤drawWidth n (countWidth B)) ∧
      Word t.val 4510 (2*j.val+1) ∧ Word t.val 4506 (RealizationParameters.detuningPrecision p S hm) ∧
      Word t.val 4541 j.val ∧ t.val.randomCursor=s.val.randomCursor+n ∧
      t.val.address=s.val.address ∧ t.val.inputHead=s.val.inputHead ∧
      t.val.memory=s.val.memory ∧ t.val.output=s.val.output ∧
      (∀i,i∉workspace→t.val.tapes i=s.val.tapes i) := by
  obtain ⟨v,bank,width,outputs⟩ := selected.parameters
  let B := Parameters.SourceOuter.outputWidth p S hm hn hm2 MasterConstants.exponent
  let n := RealizationParameters.randomBitCount p S hm
  let j := RealizationParameters.randomDraw p S hm (fun i=>tape (s.val.randomCursor+i.val))
  let v0 := initial v
  have b0 : NatAssign.Bank ids v0 s.val := by
    intro i hi
    by_cases fresh : i∈localIds
    · simp only [v0,initial,ite_eq_left fresh]
      apply (RationalAccumulator.zero_word_iff_blank _ _).mpr
      exact selected.fresh_large i (by have :=(Finset.mem_Icc.mp fresh).1;omega)
    · have member : i∈({2211,2237,2245}:Finset ℕ) := (Finset.mem_union.mp hi).resolve_left fresh
      have outer : i∈Parameters.OuterMachine.ids := by
        simp only [Finset.mem_insert,Finset.mem_singleton] at member
        rcases member with rfl|rfl|rfl <;> decide+kernel
      have fixed : Parameters.SourceOuter.relocation i=i := by
        simp only [Finset.mem_insert,Finset.mem_singleton] at member
        rcases member with rfl|rfl|rfl <;> decide+kernel
      simpa only [v0,initial,ite_eq_right fresh,fixed] using bank i outer
  have w0 : ∀i∈ids,(v0 i).bits.length≤B := by
    intro i hi
    by_cases fresh : i∈localIds
    · simp [v0,initial,fresh]
    · have member : i∈({2211,2237,2245}:Finset ℕ) := (Finset.mem_union.mp hi).resolve_left fresh
      have outer : i∈Parameters.OuterMachine.ids := by
        simp only [Finset.mem_insert,Finset.mem_singleton] at member
        rcases member with rfl|rfl|rfl <;> decide+kernel
      simpa only [v0,initial,ite_eq_right fresh] using width i outer
  obtain ⟨vm,vN,vden⟩ := source_fields p S hm v outputs
  obtain ⟨c0,a,e0,h0,ba,sa,wa,fa⟩ := count_executes v0 B w0
    (by simpa only [v0,vm] using hm)
    (by simpa only [v0,vN] using Parameters.sourceSpectralBudget_pos p S hm)
    (by rw [show v0 2237=_ from vden];positivity) input tape s b0 selected.scratch
  obtain ⟨count,blank,_,precision⟩ := countValues_fields v0
  have cn : countValues v0 4540=n := by
    simpa only [n,v0,vm,vN,RealizationParameters.randomBitCount] using count
  have pn : countValues v0 4506=RealizationParameters.detuningPrecision p S hm := by
    simpa only [v0,vm,vN,vden,Nat.clog_pow 2 _ (by decide),RealizationParameters.detuningPrecision] using precision
  have one : countValues v0 4508=1 := by
    simp [countValues,finishCount,NatAssign.values,NatAssign.Instruction.update,
      NatAssign.Instruction.value,NatAssign.Instruction.target]
  obtain ⟨c1,t,e1,h1,bt,st,wt,rt,addr,it,mt,ot,ft⟩ :=
    draw_executes (countValues v0) n (countWidth B) wa cn blank input tape a ba sa
  have sampled_eq : addressValue (RandomBitsMachine.bits tape a.val.randomCursor n)=j.val := by
    rw [fa.randomCursor,RandomBitsMachine.bits_binary_value]
    simp only [j,RealizationParameters.randomDraw,n]
  have fields := drawValues_fields (countValues v0)
    (addressValue (RandomBitsMachine.bits tape a.val.randomCursor n)) one
  refine ⟨c0+c1,t,drawValues (countValues v0) (addressValue (RandomBitsMachine.bits tape a.val.randomCursor n)),
    e0.seq e1,Nat.add_le_add h0 h1,bt,st,wt,?_,?_,?_,?_,addr.trans fa.address,
    it.trans fa.inputHead,mt.trans fa.memory,ot.trans fa.output,?_⟩
  · have word := bt 4510 (by decide)
    rw [fields.1,sampled_eq] at word
    exact word
  · have word := bt 4506 (by decide)
    rw [fields.2.1,pn] at word
    exact word
  · have word := bt 4541 (by decide)
    rw [fields.2.2,sampled_eq] at word
    exact word
  · exact rt.trans (congrArg (·+n) fa.randomCursor)
  · intro i hi
    exact (ft i hi).trans (fa.tapes i hi)

#print axioms source_executes
end Maxwell.Continuum.DetuningMachine
