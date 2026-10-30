import Maxwell.Continuum.OutputCaptureRetained
import Maxwell.Continuum.DyadicFloorData

/-! The capture compiler's exact frame transports ordinary stored-word and
arithmetic-bank contracts, including the caller's retained site count. -/
namespace Maxwell.Continuum.OutputCapture
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
open RationalDataflow

theorem Frame.tapes {archive : ℕ} {s t : Store} (h : Frame archive s t)
    (i : ℕ) (hi : i≠archive) : t.val.tapes i=s.val.tapes i := h.2.2.2.2 i hi

theorem Frame.word {archive : ℕ} {s t : Store} (h : Frame archive s t)
    (i n : ℕ) (hi : i≠archive) (hw : Word s.val i n) : Word t.val i n := by
  obtain ⟨origin,ho⟩ := hw
  exact ⟨origin,(h.tapes i hi).trans ho⟩

theorem Frame.blank {archive : ℕ} {s t : Store} (h : Frame archive s t)
    (i : ℕ) (hi : i≠archive) (hw : Blank s.val i) : Blank t.val i := by
  obtain ⟨origin,ho⟩ := hw
  exact ⟨origin,(h.tapes i hi).trans ho⟩

theorem Frame.bank {archive : ℕ} {s t : Store} (h : Frame archive s t)
    {S : Finset ℕ} {v : ℕ→ℕ} (ha : archive∉S) (hw : NatAssign.Bank S v s.val) :
    NatAssign.Bank S v t.val := by
  intro i hi
  exact h.word i (v i) (by rintro rfl;exact ha hi) (hw i hi)

theorem Frame.ready {archive : ℕ} {s t : Store} (h : Frame archive s t)
    {S : Finset ℕ} {v : ℕ→Parts} (ha : archive∉RationalDataflow.workspace S)
    (hw : Ready S v s) : Ready S v t := by
  refine ⟨h.bank (fun hi=>ha (Finset.mem_union_right _ hi)) hw.1,?_⟩
  intro i hi
  exact h.blank i (by intro he;subst archive;apply ha;simp [RationalDataflow.workspace];omega)
    (hw.2 i hi)

theorem Frame.floor_clean {archive : ℕ} {s t : Store} (h : Frame archive s t)
    (ha : archive∉({4}:Finset ℕ)∪DyadicFloor.extraIds∪NaturalQuotient.workPorts)
    (hw : DyadicFloor.Clean s.val) : DyadicFloor.Clean t.val := by
  refine ⟨h.blank 4 (by intro he;subst archive;exact ha (by simp)) hw.1,?_⟩
  intro i hi
  apply h.blank i _ (hw.2 i hi)
  intro he
  subst archive
  apply ha
  simp only [Finset.mem_union] at hi ⊢
  tauto

end Maxwell.Continuum.OutputCapture
