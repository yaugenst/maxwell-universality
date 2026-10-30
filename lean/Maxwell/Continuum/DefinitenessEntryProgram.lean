import Maxwell.Continuum.RationalDataflowTrace
import Maxwell.Continuum.RawDefiniteness

/-! A fixed four-operation machine kernel for one Schur-complement entry.
Inputs occupy words 0..3; the output is word 4 and scratch is word 5. -/

namespace Maxwell.Continuum.Calibration.RawDefiniteness

open RationalDataflow Maxwell.Cost Maxwell.Cost.Structured

def entryInstructions : List Instruction :=
  [.binary .mul 5 1 2,.inverse 4 3,.binary .mul 4 5 4,.binary .sub 4 0 4]

def entryValue (v : ℕ → Parts) : Parts :=
  (v 0).sub (((v 1).mul (v 2)).mul (v 3).inverse)

def entryOutput (v : ℕ → Parts) : ℕ → Parts :=
  Function.update (Function.update v 5 ((v 1).mul (v 2))) 4 (entryValue v)

theorem entry_evaluate (v : ℕ → Parts) : evaluate entryInstructions v=entryOutput v := by
  simp only [entryInstructions,evaluate,Instruction.update,BinaryOp.eval,
    Function.update_self,Function.update_of_ne (by decide : (3 : ℕ)≠5),
    Function.update_of_ne (by decide : (5 : ℕ)≠4),
    Function.update_of_ne (by decide : (0 : ℕ)≠4),
    Function.update_of_ne (by decide : (0 : ℕ)≠5),Function.update_idem]
  rfl

theorem entry_valid : ∀ a∈entryInstructions, a.Valid (Finset.range 6) := by
  intro a ha
  simp only [entryInstructions,List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with rfl|rfl|rfl|rfl <;> norm_num [Instruction.Valid]

theorem entry_widthTrace (v : ℕ → Parts) (W : ℕ) (hw : WidthBank (Finset.range 6) W v) :
    RationalDataflow.WidthTrace (Finset.range 6) (4*W+4) entryInstructions v := by
  have h0 := hw 0 (by decide)
  have h1 := hw 1 (by decide)
  have h2 := hw 2 (by decide)
  have h3 := hw 3 (by decide)
  have hbase := hw.mono (show W≤4*W+4 by omega)
  have hprod := h1.mul h2
  have hinv := h3.inverse
  have hmul := hprod.mul hinv
  have hresult := h0.sub hmul
  have hA := hbase.update 5 (hprod.mono (by omega))
  have hB := hA.update 4 (hinv.mono (by omega))
  have hC := hA.update 4 (hmul.mono (by omega))
  have hD := hA.update 4 (hresult.mono (by omega))
  simp only [entryInstructions,RationalDataflow.WidthTrace,Instruction.update,BinaryOp.eval,
    Instruction.LiteralFits,Function.update_self,
    Function.update_of_ne (by decide : (3 : ℕ)≠5),
    Function.update_of_ne (by decide : (5 : ℕ)≠4),
    Function.update_of_ne (by decide : (0 : ℕ)≠4),
    Function.update_of_ne (by decide : (0 : ℕ)≠5),Function.update_idem]
  exact ⟨hbase,trivial,hA,trivial,hB,trivial,hC,trivial,hD⟩

theorem entry_admissible (v : ℕ → Parts) (hp : (v 3).value≠0) :
    RationalDataflow.AdmissibleTrace entryInstructions v := by
  simp only [entryInstructions,RationalDataflow.AdmissibleTrace,Instruction.Admissible,
    Instruction.update,BinaryOp.eval,Function.update_of_ne (by decide : (3 : ℕ)≠5)]
  exact ⟨trivial,hp,trivial,trivial,trivial⟩

theorem entry_value (v : ℕ → Parts) (hg : Good (Finset.range 6) v) (hp : (v 3).value≠0) :
    (entryOutput v 4).value=(v 0).value-(v 1).value*(v 2).value/(v 3).value := by
  rw [entryOutput,Function.update_self,entryValue,Parts.sub_value _ _ (hg 0 (by decide))
    (Parts.mul_valid (Parts.mul_valid (hg 1 (by decide)) (hg 2 (by decide))) (Parts.inverse_valid hp)),
    Parts.mul_value,Parts.mul_value,Parts.inverse_value _ (hg 3 (by decide)) hp]
  rfl

theorem entry_executes (v : ℕ → Parts) (W : ℕ) (hw : WidthBank (Finset.range 6) W v)
    (input : List Bool) (tape : ℕ → Bool) (s : Store) (hs : Ready (Finset.range 6) v s) :
    ∃ cost t, Executes input tape (program entryInstructions) cost s t ∧
      cost≤4*operationCost (4*W+4)+1 ∧ Ready (Finset.range 6) (entryOutput v) t := by
  obtain ⟨cost,t,he,hc,hb,_⟩ := program_executes (Finset.range 6) entryInstructions entry_valid v
    (4*W+4) (entry_widthTrace v W hw) input tape s hs
  rw [entry_evaluate] at hb
  exact ⟨cost,t,he,hc,hb⟩

theorem entry_computes (v : ℕ → Parts) (W : ℕ) (hw : WidthBank (Finset.range 6) W v)
    (hg : Good (Finset.range 6) v) (hp : (v 3).value≠0)
    (input : List Bool) (tape : ℕ → Bool) (s : Store) (hs : Ready (Finset.range 6) v s) :
    ∃ cost t output,
      (runPriced ((program entryInstructions).compile.next input tape)
        (4*operationCost (4*W+4)+2) s.val).finished=some (t.place (program entryInstructions).size) ∧
      cost≤4*operationCost (4*W+4)+1 ∧ Ready (Finset.range 6) output t ∧
      (output 4).value=(v 0).value-(v 1).value*(v 2).value/(v 3).value := by
  obtain ⟨cost,t,he,hc,hb⟩ := entry_executes v W hw input tape s hs
  obtain ⟨hrun,_⟩ := he.compiled_run (4*operationCost (4*W+4)+2) (by omega)
  exact ⟨cost,t,entryOutput v,hrun,hc,hb,entry_value v hg hp⟩

#print axioms entry_computes

end Maxwell.Continuum.Calibration.RawDefiniteness
