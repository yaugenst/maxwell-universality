import Maxwell.Continuum.RationalDataflowExecution

/-! Literal rational loading into an existing shared register bank. -/

namespace Maxwell.Continuum.RationalDataflow
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 1000000

def literalStage (target : ℕ) (x : Parts) : List NatAssign.Instruction :=
  [.literal (positivePort target) x.positive,.literal (negativePort target) x.negative,
   .literal (denominatorPort target) x.denominator]

theorem literalStage_valid (S : Finset ℕ) (target : ℕ) (ht : target∈S) (x : Parts) :
    ∀ a∈literalStage target x, a.Valid (ids S) := by
  have hp := cell_mem ht (show positivePort target∈cellPorts target by simp [cellPorts])
  have hn := cell_mem ht (show negativePort target∈cellPorts target by simp [cellPorts])
  have hd := cell_mem ht (show denominatorPort target∈cellPorts target by simp [cellPorts])
  simp [literalStage,NatAssign.Instruction.Valid,hp,hn,hd]

theorem literalStage_values (target : ℕ) (x : Parts) (v : ℕ→Parts) :
    NatAssign.values (literalStage target x) (dataValues v)=dataValues (Function.update v target x) :=
  writeParts_dataValues v target x

theorem literalStage_width (target : ℕ) (x : Parts) (B : ℕ) (hx : x.Width B) :
    ∀ a∈literalStage target x, a.literalWidth≤B := by
  simpa only [literalStage,List.mem_cons,List.not_mem_nil,or_false,NatAssign.Instruction.literalWidth,
    forall_eq_or_imp,forall_eq,Parts.Width] using hx

theorem literal_executes (S : Finset ℕ) (target : ℕ) (ht : target∈S) (x : Parts)
    (v : ℕ→Parts) (B : ℕ) (hx : x.Width B) (hw : ∀ i∈S, (v i).Width B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : Ready S v s) :
    ∃ cost t, Executes input tape (NatAssign.code (literalStage target x)) cost s t ∧
      cost≤stageCost B ∧ Ready S (Function.update v target x) t ∧
      BinaryPrecision.Frame (workspace S) s.val t.val := by
  obtain ⟨cost,t,he,hc,hb,hsc,hf⟩ := fixedStage_executes S (literalStage target x)
    (literalStage_valid S target ht x) (by simp [literalStage]) (dataValues v) B
    (dataValues_width S v B hw) (literalStage_width target x B hx) input tape s hs.1 hs.2
  rw [literalStage_values] at hb
  exact ⟨cost,t,he,hc,⟨hb,hsc⟩,hf⟩

#print axioms literal_executes

end Maxwell.Continuum.RationalDataflow
