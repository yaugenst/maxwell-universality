import Maxwell.Continuum.CalibrationParameterSetup
import Maxwell.Continuum.ParameterSourceSelectedFrame

/-! The actual source-selected machine state supplies every calibration
dimension operand; no prepared parameter bank is a caller assumption. -/
noncomputable section
namespace Maxwell.Continuum.Calibration.SourceParameters
open Maxwell.Cost Maxwell.Cost.Structured
open RationalAccumulator (Word Blank)
set_option maxRecDepth 16000
set_option maxHeartbeats 3000000
attribute [local irreducible] MasterConstants.exponent MasterConstants.Cs
  RealizationParameters.analysisBits RealizationParameters.inputBits

def initial (log : ℕ) (v : ℕ→ℕ) (i : ℕ) : ℕ :=
  if i=2200 then log else if i∈ParameterMachine.ids then 0 else v i

def inputWidth (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz)
    (hn : 0<S.n) (hm2 : 2≤S.nnz) : ℕ :=
  Parameters.SourceOuter.outputWidth p S hm hn hm2 MasterConstants.exponent+
    (RealizationParameters.logSize S).bits.length
def code (p : Source.Parameters) : Code :=
  ParameterSetup.code (RealizationParameters.analysisBits p) (RealizationParameters.inputBits p)
def costBound (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz)
    (hn : 0<S.n) (hm2 : 2≤S.nnz) : ℕ :=
  ParameterSetup.costBound (RealizationParameters.analysisBits p) (RealizationParameters.inputBits p)
    (inputWidth p S hm hn hm2)
def width (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz)
    (hn : 0<S.n) (hm2 : 2≤S.nnz) : ℕ :=
  ParameterSetup.width (RealizationParameters.analysisBits p) (RealizationParameters.inputBits p)
    (inputWidth p S hm hn hm2)

theorem initial_fields (log : ℕ) (v : ℕ→ℕ) :
    initial log v 2200=log ∧ initial log v 2206=v 2206 ∧ initial log v 2210=v 2210 ∧
    initial log v 2221=v 2221 ∧ initial log v 2227=v 2227 := by
  simp [initial,ParameterMachine.ids]

theorem data_constant (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz)
    (e : ℕ) (v : ℕ→ℕ)
    (h : Parameters.OuterMachine.dataOf v=Parameters.SourceOuter.data p S hm e) :
    v 2210=2^e := congrArg Parameters.OuterMachine.Data.constant h

theorem executes (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz)
    (hn : 0<S.n) (hm2 : 2≤S.nnz) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (selected : Parameters.SourceSelected.Result p S hm hn hm2 MasterConstants.exponent s) :
    ∃cost t v,Executes input tape (code p) cost s t ∧ cost≤costBound p S hm hn hm2 ∧
      NatAssign.Bank ParameterInput.ids v t.val ∧ NatAssign.Scratch t.val ∧
      (∀i∈ParameterInput.ids,(v i).bits.length≤width p S hm hn hm2) ∧
      ParameterMachine.Outputs (RealizationParameters.length p S hm)
        (RealizationParameters.calibrationRadius p S hm)
        (RealizationParameters.calibrationModePrecision p S hm) v ∧
      Word t.val 4425 (RealizationParameters.templatePrecision p S) ∧
      Word t.val 4426 (RealizationParameters.materialPrecision p S) ∧
      Word t.val 4427 (RealizationParameters.sourcePrecision p S) ∧
      Word t.val 4428 (RealizationParameters.momentPrecision p S) ∧
      Word t.val 4429 (RealizationParameters.calibrationPrecision p S hm) ∧
      BinaryPrecision.Frame ParameterInput.workspace s.val t.val := by
  obtain ⟨v,bank,storedWidth,outputs⟩ := selected.parameters
  let log := RealizationParameters.logSize S
  let v0 := initial log v
  have initialized : NatAssign.Bank ParameterInput.ids v0 s.val := by
    intro i hi
    by_cases same : i=2200
    · subst i;simpa only [v0,initial,ite_true] using selected.logWord
    · by_cases fresh : i∈ParameterMachine.ids
      · simp only [v0,initial,ite_eq_right same,ite_eq_left fresh]
        apply (RationalAccumulator.zero_word_iff_blank _ _).mpr
        exact selected.fresh_large i (by have := (Finset.mem_Icc.mp fresh).1;omega)
      · have member : i∈({2200,2206,2210,2221,2227}:Finset ℕ) :=
          (Finset.mem_union.mp hi).resolve_left fresh
        have outer : i∈Parameters.OuterMachine.ids := by
          simp only [Finset.mem_insert,Finset.mem_singleton] at member
          rcases member with rfl|rfl|rfl|rfl|rfl <;> decide +kernel
        have fixed : Parameters.SourceOuter.relocation i=i := by
          simp only [Finset.mem_insert,Finset.mem_singleton] at member
          rcases member with rfl|rfl|rfl|rfl|rfl <;> decide +kernel
        simpa only [v0,initial,ite_eq_right same,ite_eq_right fresh,fixed] using bank i outer
  have width0 : ∀i∈ParameterInput.ids,(v0 i).bits.length ≤ inputWidth p S hm hn hm2 := by
    intro i hi
    by_cases same : i=2200
    · subst i
      simp only [v0,initial,ite_true,inputWidth]
      exact Nat.le_add_left _ _
    · by_cases fresh : i∈ParameterMachine.ids
      · simp only [v0,initial,ite_eq_right same,ite_eq_left fresh,
          show (0:ℕ).bits.length=0 by decide,Nat.zero_le]
      · have member : i∈({2200,2206,2210,2221,2227}:Finset ℕ) :=
          (Finset.mem_union.mp hi).resolve_left fresh
        have outer : i∈Parameters.OuterMachine.ids := by
          simp only [Finset.mem_insert,Finset.mem_singleton] at member
          rcases member with rfl|rfl|rfl|rfl|rfl <;> decide +kernel
        simpa only [v0,initial,ite_eq_right same,ite_eq_right fresh,inputWidth] using
          (storedWidth i outer).trans (Nat.le_add_right _ _)
  obtain ⟨i0,i6,i10,i21,i27⟩ := initial_fields log v
  have hC : v0 2210=2^MasterConstants.exponent := by
    rw [show v0 2210=v 2210 from i10]
    exact data_constant p S hm MasterConstants.exponent v outputs.core.data
  have hk : v0 2206=RealizationParameters.stage p S hm := i6.trans outputs.core.exponent
  have hL : v0 2221=RealizationParameters.length p S hm := i21.trans outputs.core.length
  have hd : v0 2227=RealizationParameters.spacing p S hm := by
    rw [show v0 2227=v 2227 from i27,outputs.spacing.spacing,Parameters.SourceOuter.data_input]
    rfl
  let a := RealizationParameters.analysisBits p
  let b := RealizationParameters.inputBits p
  obtain ⟨cost,t,execution,bound,bt,st,wt,result,frame⟩ := ParameterSetup.executes a b v0
    (inputWidth p S hm hn hm2) width0 hC input tape s initialized selected.scratch
  have fields := ParameterInput.source_fields p S hm v0 i0 hk hL hd hC
  dsimp only at fields
  have generic := ParameterInput.fields a b v0
  dsimp only at generic
  have hr : couplingRadius (v0 2221) (v0 2227)=RealizationParameters.calibrationRadius p S hm :=
    generic.2.1.symm.trans fields.2.1
  have hN : a*v0 2200+4*v0 2227+6*v0 2206+18=RealizationParameters.calibrationModePrecision p S hm :=
    generic.2.2.1.symm.trans fields.2.2.1
  have budget (i : ℕ) (hi : 4425 ≤ i ∧ i ≤ 4429) :
      ParameterSetup.values a b v0 i=NatAssign.values (ParameterInput.instructions a b) v0 i :=
    ParameterSetup.machine_budget _ i hi
  refine ⟨cost,t,ParameterSetup.values a b v0,execution,bound,bt,st,wt,?_,?_,?_,?_,?_,?_,frame⟩
  · rw [hr,hL,hN] at result
    exact result
  · simpa only [budget 4425 (by decide),a,b,fields.2.2.2.2.1] using bt 4425 (by decide +kernel)
  · simpa only [budget 4426 (by decide),a,b,fields.2.2.2.2.2.1] using bt 4426 (by decide +kernel)
  · simpa only [budget 4427 (by decide),a,b,fields.2.2.2.2.2.2.1] using bt 4427 (by decide +kernel)
  · simpa only [budget 4428 (by decide),a,b,fields.2.2.2.2.2.2.2.1] using bt 4428 (by decide +kernel)
  · simpa only [budget 4429 (by decide),a,b,fields.2.2.2.2.2.2.2.2] using bt 4429 (by decide +kernel)

#print axioms executes
end Maxwell.Continuum.Calibration.SourceParameters
