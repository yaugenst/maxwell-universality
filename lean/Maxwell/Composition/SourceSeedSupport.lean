import Maxwell.Composition.PhysicalSourceBudget
import Maxwell.Composition.SourceEmission

/-! The physical source uses only the original left-square source rows.
All routed subdivision vertices and physical mediators have exactly zero
source. This finite support is computed directly from the source indices. -/
noncomputable section
namespace Maxwell.Composition.SourceSeedSupport
open Maxwell.Logical
open scoped BigOperators
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 1000000

def vertex (S : Source.SparseSystem) (precision : ℕ) (i : Fin S.n) :
    SourceDecoration.Vertex S precision :=
  .inl (.inl (.inl (.inl ((sourceCircuit S precision).circuit.inputIndex i))))

theorem vertex_injective (S : Source.SparseSystem) (precision : ℕ) :
    Function.Injective (vertex S precision) := by
  intro i j h
  exact (sourceCircuit S precision).circuit.inputIndex_injective
    (Sum.inl.inj (Sum.inl.inj (Sum.inl.inj (Sum.inl.inj h))))

theorem source_at (S : Source.SparseSystem) (precision : ℕ) (i : Fin S.n) :
    SourceRational.decorated S precision (vertex S precision i) =
      Normalization.normalizedSource S i := by
  simp only [vertex,SourceRational.decorated,SourceRational.routed,SourceRational.positive,
    SourceRational.boundary,(sourceCircuit S precision).circuit.inputIndex_value,i.isLt,↓reduceDIte]

theorem source_support (S : Source.SparseSystem) (precision : ℕ)
    (v : SourceDecoration.Vertex S precision) (hv : SourceRational.decorated S precision v ≠ 0) :
    ∃ i, vertex S precision i = v := by
  cases v with
  | inr e => exact False.elim (hv rfl)
  | inl v => cases v with
    | inr e => exact False.elim (hv rfl)
    | inl v => cases v with
      | inr e => exact False.elim (hv rfl)
      | inl v => cases v with
        | inr j => exact False.elim (hv rfl)
        | inl j =>
          have hj : j.val<S.n := by
            by_contra hn
            exact hv (by simp [SourceRational.decorated,SourceRational.routed,
              SourceRational.positive,SourceRational.boundary,hn])
          refine ⟨⟨j.val,hj⟩,?_⟩
          unfold vertex
          congr 4
          exact Fin.ext ((sourceCircuit S precision).circuit.inputIndex_value ⟨j.val,hj⟩)

theorem weighted_sum (S : Source.SparseSystem) (precision : ℕ)
    (f : SourceDecoration.Vertex S precision → ℚ) :
    ∑ v, f v*SourceRational.decorated S precision v =
      ∑ i, f (vertex S precision i)*Normalization.normalizedSource S i := by
  classical
  have hs : (∑ v ∈ Finset.univ.image (vertex S precision),
      f v*SourceRational.decorated S precision v) =
      ∑ v, f v*SourceRational.decorated S precision v := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro v _ hv
    have hz : SourceRational.decorated S precision v = 0 := by
      by_contra hn
      obtain ⟨i,rfl⟩ := source_support S precision v hn
      exact hv (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
    rw [hz,mul_zero]
  rw [←hs,Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro i _
    rw [source_at]
  · intro i _ j _ h
    exact vertex_injective S precision h

/-- The selected source terminal is already among the initial original
vertices; no path enumeration is needed to locate it. -/
theorem original_index (S : Source.SparseSystem) (precision : ℕ) (i : Fin S.n) :
    (SourceEnumeration.vertexEquiv S precision
      (.inl (.inl ((sourceCircuit S precision).circuit.inputIndex i)))).val = i.val := by
  simp only [SourceEnumeration.vertexEquiv,Equiv.trans_apply,Equiv.sumCongr_apply]
  exact (sourceCircuit S precision).circuit.inputIndex_value i

end Maxwell.Composition.SourceSeedSupport
