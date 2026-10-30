import Maxwell.Composition.SourceDecoration
import Maxwell.Composition.PhysicalParameters

/-! Bounds for all actual wells, including every midpoint mediator. -/

noncomputable section
namespace Maxwell.Continuum.Parameters
open Maxwell.Composition Maxwell.Spectral.Lattice Maxwell.Logical.Routing

theorem sourceEdge_axis_injective (S : Source.SparseSystem) (precision : ℕ) :
    Function.Injective (fun e : SourceIncidence.E S precision =>
      (e.val.1, SourceIncidence.axis S precision e)) := by
  intro a b h
  have hv : a.val.1 = b.val.1 := congrArg
    (fun x : SourceIncidence.V S precision × Fin 3 => x.1) h
  have hk : SourceIncidence.axis S precision a = SourceIncidence.axis S precision b := congrArg
    (fun x : SourceIncidence.V S precision × Fin 3 => x.2) h
  apply Subtype.ext
  apply Prod.ext hv
  apply SourceDefectLayout.position_injective S precision
  exact (SourceIncidence.axis_spec S precision a).trans
    ((congrArg₂ (fun v j => SourceIncidence.position S precision v+
      Maxwell.Spectral.Lattice.unitSite j) hv hk).trans (SourceIncidence.axis_spec S precision b).symm)

theorem sourceEdge_card (S : Source.SparseSystem) (precision : ℕ) :
    Fintype.card (SourceIncidence.E S precision) ≤ 3*Fintype.card (SourceRouting.Vertex S precision) := by
  have h := Fintype.card_le_of_injective _ (sourceEdge_axis_injective S precision)
  simpa only [Fintype.card_prod, Fintype.card_fin, Nat.mul_comm] using h

theorem sourceWell_card (S : Source.SparseSystem) (precision : ℕ) :
    Fintype.card (SourceDecoration.Vertex S precision) ≤ 4*Fintype.card (SourceRouting.Vertex S precision) := by
  have h := sourceEdge_card S precision
  change Fintype.card (SourceIncidence.V S precision ⊕ SourceIncidence.E S precision) ≤ _
  rw [Fintype.card_sum]
  change Fintype.card (SourceRouting.Vertex S precision)+Fintype.card (SourceIncidence.E S precision) ≤ _
  omega

theorem sourceSite_coordinate (S : Source.SparseSystem) (precision : ℕ)
    (v : SourceDecoration.Vertex S precision) (j : Fin 3) :
    0 ≤ SourceDecoration.site S precision v j ∧
    SourceDecoration.site S precision v j ≤ (258*PhysicalParameters.routingSide S precision : ℕ) := by
  have h := SourceDecoration.site_inside S precision v j
  have hp := SourceRouting.side_pos S precision
  rw [PhysicalParameters.routingSide_eq]
  refine ⟨h.1, h.2.le.trans ?_⟩
  have hs : Green.boxSide (SourceDecoration.baseBox S precision) j ≤
      258*SourceRouting.side S precision := by
    fin_cases j <;> dsimp [Green.boxSide, SourceDecoration.baseBox, SourceDefectLayout.baseBox,
      boxSideXY, boxSideZ] <;> omega
  exact_mod_cast hs

#print axioms sourceWell_card
#print axioms sourceSite_coordinate

end Maxwell.Continuum.Parameters
