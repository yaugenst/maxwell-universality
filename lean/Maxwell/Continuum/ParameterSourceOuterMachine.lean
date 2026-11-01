import Maxwell.Continuum.ParameterSourceOuterData
import Maxwell.Continuum.ParameterOuterMachine
import Maxwell.Cost.Structured.RenameFrame

/-! The actual selected continuum parameters are computed from the source
front end's stored operands, with retained low tapes protected by renaming. -/
noncomputable section
namespace Maxwell.Continuum.Parameters.SourceOuter
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Composition
open RationalAccumulator (Word Blank)
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

def sourceValues (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz) (e : ℕ) : ℕ→ℕ :=
  initial ⌈p.conditionExponent⌉₊ ⌈p.accuracyExponent⌉₊ e S (SelectedInput.input p S hm).precision
def sourceWidth (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz) (e : ℕ) : ℕ :=
  inputWidth ⌈p.conditionExponent⌉₊ ⌈p.accuracyExponent⌉₊ e S (SelectedInput.input p S hm).precision

theorem source_positive (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz)
    (hn : 0<S.n) (hm2 : 2≤S.nnz) (e : ℕ) : (OuterMachine.dataOf (sourceValues p S hm e)).Positive := by
  rw [sourceValues,data_initial p S hm hn hm2 e]
  exact data_positive p S hm e

theorem log_positive (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz) (e : ℕ) :
    0<sourceValues p S hm e 2200 := by
  rw [sourceValues,(initial_fields _ _ _ _ _).1]
  exact inputLog_pos S.nnz

def code : Code := .call (OuterMachine.code.compile.renameTapes relocation)
def work : Finset ℕ := OuterMachine.workspace.image relocation
def cost (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz)
    (hn : 0<S.n) (hm2 : 2≤S.nnz) (e : ℕ) : ℕ :=
  OuterMachine.costBound (sourceValues p S hm e) (source_positive p S hm hn hm2 e) e
    (sourceWidth p S hm e) (log_positive p S hm e)+1
def outputWidth (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz)
    (hn : 0<S.n) (hm2 : 2≤S.nnz) (e : ℕ) : ℕ :=
  OuterMachine.resultWidth (sourceValues p S hm e) (source_positive p S hm hn hm2 e) e
    (sourceWidth p S hm e) (log_positive p S hm e)
def exponent (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz) (e : ℕ) : ℕ :=
  selectedOuterExponent (sourceInput p S hm) e (minimumLengthExponent e) (inputLog S.nnz) (inputLog_pos S.nnz)

theorem executes (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz)
    (hn : 0<S.n) (hm2 : 2≤S.nnz) (e : ℕ) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : SourceExecution.Result ⌈p.conditionExponent⌉₊ ⌈p.accuracyExponent⌉₊ e S
      (SelectedInput.input p S hm).precision s) :
    ∃steps t w,Executes input tape code steps s t ∧ steps≤cost p S hm hn hm2 e ∧
      (∀i∈OuterMachine.ids,Word t.val (relocation i) (w i)) ∧ NatAssign.Scratch t.val ∧
      (∀i∈OuterMachine.ids,(w i).bits.length≤outputWidth p S hm hn hm2 e) ∧
      OuterMachine.StageOutputs (data p S hm e) (data_positive p S hm e) e (exponent p S hm e) w ∧
      BinaryPrecision.Frame work s.val t.val ∧ Word t.val 2200 (inputLog S.nnz) := by
  have fields:=initial_fields ⌈p.conditionExponent⌉₊ ⌈p.accuracyExponent⌉₊ e S (SelectedInput.input p S hm).precision
  have hd:=data_initial p S hm hn hm2 e
  have constant : sourceValues p S hm e 2210=2^e := by
    have h:=congrArg OuterMachine.Data.constant hd
    exact h
  obtain ⟨steps,u,w,he,hcost,bu,su,wu,output,frame,log⟩:=OuterMachine.executes (sourceValues p S hm e)
    (source_positive p S hm hn hm2 e) e (sourceWidth p S hm e) (log_positive p S hm e)
    constant (fun i _=>initial_width _ _ _ _ _ i) input tape (s.renameTapes relocation) (bank hs) (scratch hs)
  let t:=u.renameTapes relocation
  have exec : Executes input tape code (steps+1) s t := by
    have hh:=he.renamed_call relocation
    have restore : (s.renameTapes relocation).renameTapes relocation=s := Store.renameTapes_symm relocation s
    rw [restore] at hh
    exact hh
  have framed : BinaryPrecision.Frame work s.val t.val := by
    have ff:=frame.renameTapes relocation
    change BinaryPrecision.Frame work ((s.renameTapes relocation).renameTapes relocation).val t.val at ff
    have restore : (s.renameTapes relocation).renameTapes relocation=s := Store.renameTapes_symm relocation s
    rw [restore] at ff
    exact ff
  refine ⟨steps+1,t,w,exec,Nat.add_le_add_right hcost 1,?_,?_,wu,?_,framed,?_⟩
  · intro i hi
    exact BankArray.Word.renameTapes (bu i hi) relocation
  · intro i hi
    have fixed : relocation i=i := TapeBlockSwap.apply_outside 4 1257 3000 (by decide) i
      (Or.inl hi) (Or.inl (by omega))
    obtain ⟨origin,word⟩:=su i (by omega)
    exact ⟨origin,((renamed_tape u i).trans (congrArg u.val.tapes fixed)).trans word⟩
  · simpa only [sourceValues,hd,data_input,fields.1,fields.2,exponent] using output
  · have kept:=BankArray.Word.renameTapes log relocation
    have fixed : relocation 2200=2200 := by decide +kernel
    simpa only [Word,BankArray.Word,t,Store.renameTapes,fixed,sourceValues,fields.1] using kept

#print axioms executes
end Maxwell.Continuum.Parameters.SourceOuter
