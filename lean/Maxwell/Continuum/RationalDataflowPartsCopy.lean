import Maxwell.Continuum.NaturalBankStage
import Maxwell.Continuum.RationalDataflowTrace

/-! Exact copying of the three raw integer channels between logical
registers, with charged erasure of the previous destination. -/
namespace Maxwell.Continuum.RationalDataflow
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 3000000

def partsCopyStage (source target : ℕ) : List NatAssign.Instruction :=
  [.copy (positivePort source) (positivePort target),
   .copy (negativePort source) (negativePort target),
   .copy (denominatorPort source) (denominatorPort target)]
def partsCopyCode (source target : ℕ) : Code := NatAssign.code (partsCopyStage source target)

theorem partsCopy_values (source target : ℕ) (v : ℕ→Parts) :
    NatAssign.values (partsCopyStage source target) (dataValues v)=
      dataValues (Function.update v target (v source)) := by
  rw [←writeParts_dataValues]
  have neq : negativePort source≠positivePort target ∧
      denominatorPort source≠positivePort target ∧ denominatorPort source≠negativePort target := by
    simp only [positivePort,negativePort,denominatorPort]
    omega
  simp only [partsCopyStage,NatAssign.values,NatAssign.Instruction.update,
    NatAssign.Instruction.target,NatAssign.Instruction.value,Function.update_of_ne neq.1,
    Function.update_of_ne neq.2.1,Function.update_of_ne neq.2.2,
    dataValues_positive,dataValues_negative,dataValues_denominator,writeParts]

theorem partsCopy_executes (S : Finset ℕ) (source target : ℕ)
    (hs : source∈S) (ht : target∈S) (hne : source≠target)
    (v : ℕ→Parts) (B : ℕ) (hw : WidthBank S B v)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hr : Ready S v s) :
    ∃cost t,Executes input tape (partsCopyCode source target) cost s t ∧ cost ≤ stageCost B ∧
      Ready S (Function.update v target (v source)) t ∧
      WidthBank S B (Function.update v target (v source)) ∧
      BinaryPrecision.Frame (workspace S) s.val t.val := by
  have hv : ∀a∈partsCopyStage source target,a.Valid (ids S) := by
    intro a ha
    simp only [partsCopyStage,List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl
    all_goals
      refine ⟨cell_mem hs (by simp [cellPorts]),cell_mem ht (by simp [cellPorts]),?_⟩
      simp only [positivePort,negativePort,denominatorPort]
      omega
  obtain ⟨c,t,e,hc,bt,zt,ft⟩ := fixedBankStage_executes (ids S) (ids_ge S)
    (partsCopyStage source target) hv (by simp [partsCopyStage]) (dataValues v) B
    (dataValues_width S v B hw) (by simp [partsCopyStage,NatAssign.Instruction.literalWidth])
    input tape s hr.1 hr.2
  rw [partsCopy_values source target v] at bt
  exact ⟨c,t,e,hc,⟨bt,zt⟩,hw.update target (hw source hs),ft⟩

#print axioms partsCopy_executes
end Maxwell.Continuum.RationalDataflow
