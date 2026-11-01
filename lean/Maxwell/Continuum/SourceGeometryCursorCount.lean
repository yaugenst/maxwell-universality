import Maxwell.Continuum.SourceGeometryPathCounts

/-! Recover the actual number of wells from the produced geometry cursor.
The two subtractions count internal vertices and path segments exactly. -/
namespace Maxwell.Composition.SourceDecorationEnumeration
open Maxwell.Logical Maxwell.Logical.Routing Maxwell.Spectral.Lattice Maxwell.Cost
set_option maxHeartbeats 2200000
set_option maxRecDepth 16384

theorem sum_sub_add {α : Type*} (xs : List α) (f : α→ℕ) (trim : ℕ)
    (h : ∀x∈xs,trim≤f x) :
    (xs.map (fun x=>f x-trim)).sum+trim*xs.length=(xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx:=h x (by simp)
    have hs:=ih (fun y hy=>h y (by simp [hy]))
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.mul_add,Nat.mul_one]
    omega

theorem siteCount_cursor_identity {v e : ℕ} (saved : SourceEmission.Geometry v e)
    (two : ∀i,2≤(saved.paths.get i).length) :
    3*siteCount saved+3*v+11*e=2*packedLength saved := by
  have h₂:=sum_sub_add (List.finRange e) (fun i=>(saved.paths.get i).length) 2
    (fun i _=>two i)
  have h₁:=sum_sub_add (List.finRange e) (fun i=>(saved.paths.get i).length) 1
    (fun i _=>by have h:=two i;omega)
  simp only [List.length_finRange] at h₁ h₂
  unfold siteCount packedLength
  omega

theorem siteCount_from_cursor {v e : ℕ} (saved : SourceEmission.Geometry v e)
    (two : ∀i,2≤(saved.paths.get i).length) :
    siteCount saved=(2*packedLength saved-3*v-11*e)/3 := by
  have h:=siteCount_cursor_identity saved two
  omega

noncomputable section
variable (S : Source.SparseSystem) (precision : ℕ)

theorem Represents.card_from_cursor {saved} (h : Represents S precision saved) :
    Fintype.card (SourceDecoration.Vertex S precision)=
      (2*packedLength saved-
        3*((sourceCircuit S precision).size+(sourceCircuit S precision).size+
          (sourceSquareEntries S precision).length)-
        11*((sourceSquareEntries S precision).length+(sourceSquareEntries S precision).length))/3 := by
  rw [←h.siteCount_eq]
  exact siteCount_from_cursor saved h.path_length_two

#print axioms Represents.card_from_cursor
end
end Maxwell.Composition.SourceDecorationEnumeration
