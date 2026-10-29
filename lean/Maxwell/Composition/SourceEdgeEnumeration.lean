import Maxwell.Composition.SourceSteps
import Maxwell.Composition.SourceIncidence

/-! Chronological path steps enumerate exactly the canonical oriented edges.
This correspondence never scans all pairs of routed vertices. -/
noncomputable section
namespace Maxwell.Composition.SourceEdgeEnumeration
open SourceSteps
attribute [local instance] Classical.propDecidable
variable (S : Source.SparseSystem) (precision : ℕ)

private theorem height_ne (s : Step S precision) :
    SourceIncidence.height (SourceIncidence.position S precision (left S precision s)) ≠
      SourceIncidence.height (SourceIncidence.position S precision (right S precision s)) :=
  SourceIncidence.adjacent_height_ne _ _
    (SourceIncidence.matrix_adjacent S precision _ _ (distinct S precision s)
      (by rw [matrix_step]; norm_num))

/-- The orientation uses one integer comparison of the two path samples. -/
def toEdge (s : Step S precision) : SourceIncidence.E S precision :=
  if h : SourceIncidence.height (SourceIncidence.position S precision (left S precision s)) <
      SourceIncidence.height (SourceIncidence.position S precision (right S precision s)) then
    ⟨(left S precision s, right S precision s), matrix_step S precision s, h⟩
  else
    ⟨(right S precision s, left S precision s), by
      rw [← SourceSubdivision.matrix_symmetric S precision]
      exact matrix_step S precision s, by dsimp only; have := height_ne S precision s; omega⟩

theorem toEdge_endpoints (s : Step S precision) :
    ((toEdge S precision s).val.1 = left S precision s ∧
      (toEdge S precision s).val.2 = right S precision s) ∨
    ((toEdge S precision s).val.1 = right S precision s ∧
      (toEdge S precision s).val.2 = left S precision s) := by
  by_cases h : SourceIncidence.height (SourceIncidence.position S precision (left S precision s)) <
      SourceIncidence.height (SourceIncidence.position S precision (right S precision s))
  · simp only [toEdge, h, ↓reduceDIte]; exact Or.inl ⟨True.intro, True.intro⟩
  · simp only [toEdge, h, ↓reduceDIte]; exact Or.inr ⟨True.intro, True.intro⟩

theorem toEdge_injective : Function.Injective (toEdge S precision) := by
  intro a b he
  have ht := congrArg (fun e : SourceIncidence.E S precision => e.val.1) he
  have hh := congrArg (fun e : SourceIncidence.E S precision => e.val.2) he
  apply unordered_injective S precision a b
  rcases toEdge_endpoints S precision a with ha | ha <;>
    rcases toEdge_endpoints S precision b with hb | hb
  · exact Or.inl ⟨ha.1.symm.trans (ht.trans hb.1), ha.2.symm.trans (hh.trans hb.2)⟩
  · exact Or.inr ⟨ha.1.symm.trans (ht.trans hb.1), ha.2.symm.trans (hh.trans hb.2)⟩
  · exact Or.inr ⟨ha.2.symm.trans (hh.trans hb.2), ha.1.symm.trans (ht.trans hb.1)⟩
  · exact Or.inl ⟨ha.2.symm.trans (hh.trans hb.2), ha.1.symm.trans (ht.trans hb.1)⟩

theorem toEdge_surjective : Function.Surjective (toEdge S precision) := by
  intro e
  obtain ⟨s, hs⟩ := matrix_support S precision e.val.1 e.val.2
    ((SourceIncidence.graph S precision).distinct e) (by rw [e.property.1]; norm_num)
  refine ⟨s, ?_⟩
  have hc := toEdge_endpoints S precision s
  have horder := e.property.2
  have hcorder := (toEdge S precision s).property.2
  apply Subtype.ext
  rcases hs with hs | hs <;> rcases hc with hc | hc
  · exact Prod.ext (hc.1.trans hs.1.symm) (hc.2.trans hs.2.symm)
  · rw [hc.1, hc.2, ← hs.1, ← hs.2] at hcorder
    omega
  · rw [hc.1, hc.2, ← hs.2, ← hs.1] at hcorder
    omega
  · exact Prod.ext (hc.1.trans hs.1.symm) (hc.2.trans hs.2.symm)

/-- A semantic equivalence certifying the chronological enumeration.
Only its forward integer orientation is used by the finite emitter. -/
def equiv : Step S precision ≃ SourceIncidence.E S precision :=
  Equiv.ofBijective (toEdge S precision) ⟨toEdge_injective S precision, toEdge_surjective S precision⟩

@[simp] theorem equiv_apply (s : Step S precision) : equiv S precision s = toEdge S precision s := rfl

end Maxwell.Composition.SourceEdgeEnumeration
