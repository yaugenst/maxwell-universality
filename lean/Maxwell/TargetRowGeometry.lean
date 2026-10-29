import Maxwell.TargetGeometry

/-!
# Uniform row incidence bound for the relative-PEC curl

A square face has four geometric boundary edges. Retained electric edges
embed injectively into the full edge set, so deleting PEC boundary edges
cannot increase this row count.
-/

namespace Maxwell.Target

/-- All electric edges before deleting tangential PEC boundary edges. -/
abbrev Box.FullEdge (B : Box) :=
  (Fin B.nx × Fin (B.ny + 1) × Fin (B.nz + 1)) ⊕
    ((Fin (B.nx + 1) × Fin B.ny × Fin (B.nz + 1)) ⊕
      (Fin (B.nx + 1) × Fin (B.ny + 1) × Fin B.nz))

/-- The geometric position of a retained edge in the full edge set. -/
def fullEdge {B : Box} : B.Edge → B.FullEdge
  | .inl (i, j, k) => .inl (i, interiorVertex j, interiorVertex k)
  | .inr (.inl (i, j, k)) => .inr (.inl (interiorVertex i, j, interiorVertex k))
  | .inr (.inr (i, j, k)) => .inr (.inr (interiorVertex i, interiorVertex j, k))

theorem fullEdge_injective {B : Box} : Function.Injective (@fullEdge B) := by
  rintro (⟨i, j, k⟩ | (⟨i, j, k⟩ | ⟨i, j, k⟩))
    (⟨i', j', k'⟩ | (⟨i', j', k'⟩ | ⟨i', j', k'⟩)) h <;>
    simp_all [fullEdge, Fin.ext_iff, interiorVertex]

/-- The four full boundary edges of a face. -/
def boundaryEdges {B : Box} : B.Face → Fin 4 → B.FullEdge
  | .inl (i, j, k) =>
      ![.inr (.inl (i, j, k.castSucc)),
        .inr (.inl (i, j, k.succ)),
        .inr (.inr (i, j.castSucc, k)),
        .inr (.inr (i, j.succ, k))]
  | .inr (.inl (i, j, k)) =>
      ![.inr (.inr (i.castSucc, j, k)),
        .inr (.inr (i.succ, j, k)),
        .inl (i, j, k.castSucc),
        .inl (i, j, k.succ)]
  | .inr (.inr (i, j, k)) =>
      ![.inl (i, j.castSucc, k),
        .inl (i, j.succ, k),
        .inr (.inl (i.castSucc, j, k)),
        .inr (.inl (i.succ, j, k))]

theorem fullEdge_mem_boundary {B : Box} (e : B.Edge) (a : Fin 4) :
    ∃ b, fullEdge e = boundaryEdges (incidentFaces e a) b := by
  refine ⟨![3, 2, 1, 0] a, ?_⟩
  rcases e with (⟨i, j, k⟩ | (⟨i, j, k⟩ | ⟨i, j, k⟩)) <;>
    fin_cases a <;>
    simp [fullEdge, boundaryEdges, incidentFaces,
      interiorVertex, interiorLower, interiorUpper]

/-- Every nonzero row entry comes from a geometric boundary edge. -/
theorem curl_ne_zero_boundary {B : Box} (f : B.Face) (e : B.Edge)
    (h : curl B f e ≠ 0) :
    fullEdge e ∈ Finset.univ.image (boundaryEdges f) := by
  obtain ⟨a, rfl⟩ := (curl_ne_zero_iff e f).mp h
  obtain ⟨b, hb⟩ := fullEdge_mem_boundary e a
  exact Finset.mem_image.mpr ⟨b, Finset.mem_univ _, hb.symm⟩

/-- A relative-PEC curl row has at most four nonzero entries. -/
theorem curl_row_nnz {B : Box} (f : B.Face) :
    (Finset.univ.filter (fun e : B.Edge => curl B f e ≠ 0)).card ≤ 4 := by
  let s := Finset.univ.filter (fun e : B.Edge => curl B f e ≠ 0)
  have hsub : s.image fullEdge ⊆ Finset.univ.image (boundaryEdges f) := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
    exact curl_ne_zero_boundary f e (Finset.mem_filter.mp he).2
  calc
    s.card = (s.image fullEdge).card :=
      (Finset.card_image_of_injective s fullEdge_injective).symm
    _ ≤ (Finset.univ.image (boundaryEdges f)).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Fin 4)).card := Finset.card_image_le
    _ = 4 := by simp

/-- Each nonzero oriented incidence has absolute value one. -/
theorem curl_abs_eq_one {B : Box} (f : B.Face) (e : B.Edge)
    (h : curl B f e ≠ 0) : |curl B f e| = 1 := by
  obtain ⟨a, rfl⟩ := (curl_ne_zero_iff e f).mp h
  rw [curl_incident]
  exact incidenceSign_abs a

/-- The absolute row sum of the relative-PEC curl is bounded by four,
independently of box dimensions. -/
theorem curl_row_l1 {B : Box} (f : B.Face) :
    ∑ e : B.Edge, |curl B f e| ≤ 4 := by
  have heq : (∑ e : B.Edge, |curl B f e|) =
      ((Finset.univ.filter (fun e : B.Edge => curl B f e ≠ 0)).card : ℚ) := by
    rw [← Finset.sum_filter_ne_zero]
    have hfilter : Finset.univ.filter (fun e : B.Edge => |curl B f e| ≠ 0) =
        Finset.univ.filter (fun e : B.Edge => curl B f e ≠ 0) := by
      ext e
      simp
    rw [hfilter]
    simp only [Finset.card_eq_sum_ones]
    push_cast
    apply Finset.sum_congr rfl
    intro e he
    exact curl_abs_eq_one f e (Finset.mem_filter.mp he).2
  rw [heq]
  exact_mod_cast curl_row_nnz f

/-- The curl Gram matrix has a dimension-independent absolute row sum. -/
theorem curl_gram_row_l1 {B : Box} (e : B.Edge) :
    ∑ j : B.Edge, |((curl B).transpose * curl B) e j| ≤ 16 := by
  calc
    (∑ j : B.Edge, |((curl B).transpose * curl B) e j|) ≤
        ∑ j : B.Edge, ∑ f : B.Face, |curl B f e| * |curl B f j| := by
      apply Finset.sum_le_sum
      intro j _
      simpa only [Matrix.mul_apply, Matrix.transpose_apply, abs_mul] using
        Finset.abs_sum_le_sum_abs (fun f : B.Face => curl B f e * curl B f j)
          Finset.univ
    _ = ∑ f : B.Face, |curl B f e| * (∑ j : B.Edge, |curl B f j|) := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ ≤ ∑ f : B.Face, |curl B f e| * 4 := by
      apply Finset.sum_le_sum
      intro f _
      exact mul_le_mul_of_nonneg_left (curl_row_l1 f) (abs_nonneg _)
    _ = 16 := by rw [← Finset.sum_mul, curl_column_abs_sum]; norm_num

/-- The admissible scalar Maxwell operator has absolute row sum at most
sixteen, since its positive mass subtraction reduces the Gram diagonal. -/
theorem maxwell_row_l1 {B : Box}
    (material : ScalarMaterial B.nx B.ny B.nz) (e : B.Edge) :
    ∑ j : B.Edge, |maxwell material e j| ≤ 16 := by
  calc
    (∑ j : B.Edge, |maxwell material e j|) ≤
        ∑ j : B.Edge, |((curl B).transpose * curl B) e j| :=
      Finset.sum_le_sum (fun j _ => maxwell_abs_le_gram material e j)
    _ ≤ 16 := curl_gram_row_l1 e

/-- Symmetry gives the identical absolute column bound. -/
theorem maxwell_column_l1 {B : Box}
    (material : ScalarMaterial B.nx B.ny B.nz) (e : B.Edge) :
    ∑ j : B.Edge, |maxwell material j e| ≤ 16 := by
  simpa only [(maxwell_symmetric material).apply e] using maxwell_row_l1 material e

/-- Reversing the four boundary slots identifies the column-defined
incidence with the corresponding forward row incidence. -/
theorem curl_row_incidence_iff {B : Box} (f : B.Face) (e : B.Edge) (a : Fin 4) :
    f = incidentFaces e a ↔
      fullEdge e = boundaryEdges f (![3, 2, 1, 0] a) := by
  rcases f with (⟨i, j, k⟩ | (⟨i, j, k⟩ | ⟨i, j, k⟩)) <;>
    rcases e with (⟨i', j', k'⟩ | (⟨i', j', k'⟩ | ⟨i', j', k'⟩)) <;>
    fin_cases a <;>
    simp [incidentFaces, fullEdge, boundaryEdges, interiorVertex,
      interiorLower, interiorUpper, Fin.ext_iff] <;> omega

/-- Exact forward curl convention: every face row is its four geometric
boundary edges with coefficients `+1,-1,-1,+1`; deleted PEC edges are absent. -/
theorem curl_row_formula {B : Box} (f : B.Face) (e : B.Edge) :
    curl B f e =
      ∑ b : Fin 4, if fullEdge e = boundaryEdges f b then incidenceSign b else 0 := by
  simp only [curl, curl_row_incidence_iff, Fin.sum_univ_four]
  norm_num [incidenceSign]
  ac_rfl

end Maxwell.Target
