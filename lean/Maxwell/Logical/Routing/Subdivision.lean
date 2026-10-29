import Maxwell.Logical.Routing.EdgeWalk

/-! Direct sequential subdivision vertices and their actual cubic embedding. -/

namespace Maxwell.Logical.Routing.Subdivision

open Maxwell.Logical.Routing
open Maxwell.Logical.Routing.SortSchedule
open Maxwell.Logical.Routing.Gluing
open Maxwell.Logical.Routing.EdgeWalk

/-- The original vertices together with sequentially indexed internal
vertices on each original graph edge. -/
def Vertex {V E : Type*} {half : ℕ} (data : Data V E half) :=
  V ⊕ (Σ e : E, Fin ((edgeWalk data e).length - 1))

noncomputable def embedding {V E : Type*} {half : ℕ} (data : Data V E half) : Vertex data → Point
  | .inl v => vertexPoint data v
  | .inr ⟨e, t⟩ => (edgeWalk data e).point (t.val + 1)

/-- The direct path indexing gives a globally injective subdivision embedding. -/
theorem embedding_injective {V E : Type*} {half : ℕ} (data : Data V E half) :
    Function.Injective (embedding data) := by
  intro a b he
  cases a with
  | inl a =>
    cases b with
    | inl b => exact congrArg Sum.inl (vertexPoint_injective data he)
    | inr b =>
      rcases b with ⟨e, t⟩
      have ht := t.isLt
      have hh := edgeWalk_meets_vertex data e a (t.val + 1) (by omega) he.symm
      obtain ⟨side, _, hi⟩ := hh
      cases side <;> simp only [Bool.false_eq_true, ↓reduceIte] at hi <;> omega
  | inr a =>
    rcases a with ⟨e, t⟩
    cases b with
    | inl b =>
      have ht := t.isLt
      have hh := edgeWalk_meets_vertex data e b (t.val + 1) (by omega) he
      obtain ⟨side, _, hi⟩ := hh
      cases side <;> simp only [Bool.false_eq_true, ↓reduceIte] at hi <;> omega
    | inr b =>
      rcases b with ⟨f, u⟩
      have ht := t.isLt
      have hu := u.isLt
      by_cases hef : e = f
      · subst f
        have hh := edgeWalk_simple data e (t.val + 1) (u.val + 1) (by omega) (by omega) he
        have htu : t = u := Fin.ext (by omega)
        subst u
        rfl
      · obtain ⟨side, _, hh, _⟩ := edgeWalk_intersection data e f hef
          (t.val + 1) (u.val + 1) (by omega) (by omega) he
        have hi := edgeWalk_endpoint_index data e side (t.val + 1) (by omega) hh
        cases side <;> simp only [Bool.false_eq_true, ↓reduceIte] at hi <;> omega

/-- A chronological edge-path vertex, with shared endpoints stored as the
original vertices rather than duplicated subdivision vertices. -/
noncomputable def edgeVertex {V E : Type*} {half : ℕ} (data : Data V E half) (e : E)
    (t : Fin ((edgeWalk data e).length + 1)) : Vertex data :=
  if h0 : t.val = 0 then .inl (data.endpoint e false)
  else if hlast : t.val = (edgeWalk data e).length then .inl (data.endpoint e true)
  else .inr ⟨e, ⟨t.val - 1, by have ht := t.isLt; omega⟩⟩

/-- The sequential subdivision coordinates are exactly the constructed walk samples. -/
theorem embedding_edgeVertex {V E : Type*} {half : ℕ} (data : Data V E half) (e : E)
    (t : Fin ((edgeWalk data e).length + 1)) :
    embedding data (edgeVertex data e t) = (edgeWalk data e).point t.val := by
  by_cases h0 : t.val = 0
  · simp only [edgeVertex, h0, ↓reduceDIte, embedding]
    exact (edgeWalk data e).first.symm
  · by_cases hlast : t.val = (edgeWalk data e).length
    · have hv : edgeVertex data e t = Sum.inl (data.endpoint e true) := by
        simp only [edgeVertex, h0, ↓reduceDIte]
        simp only [hlast, ↓reduceDIte]
        rfl
      rw [hv]
      change vertexPoint data (data.endpoint e true) = (edgeWalk data e).point t.val
      rw [hlast]
      exact (edgeWalk data e).last.symm
    · have he : t.val - 1 + 1 = t.val := by omega
      simp only [edgeVertex, h0, hlast, ↓reduceDIte, embedding, he]

/-- Every consecutive subdivision pair is a genuine unit cubic-lattice edge. -/
theorem edgeVertex_unit_steps {V E : Type*} {half : ℕ} (data : Data V E half) (e : E)
    (t : Fin (edgeWalk data e).length) :
    UnitAdjacent (embedding data (edgeVertex data e t.castSucc))
      (embedding data (edgeVertex data e t.succ)) := by
  rw [embedding_edgeVertex, embedding_edgeVertex]
  exact (edgeWalk data e).step t.val t.isLt

theorem edgeVertex_injective {V E : Type*} {half : ℕ} (data : Data V E half) (e : E) :
    Function.Injective (edgeVertex data e) := by
  intro s t he
  have hh := congrArg (embedding data) he
  rw [embedding_edgeVertex, embedding_edgeVertex] at hh
  exact Fin.ext (edgeWalk_simple data e s.val t.val (by omega) (by omega) hh)

/-- The number of internal vertices is exactly a multiple of four. -/
theorem internal_count_wire_form {V E : Type*} {half : ℕ} (data : Data V E half) (e : E) :
    ∃ j : ℕ, (edgeWalk data e).length - 1 = 4 * j := by
  obtain ⟨j, hj⟩ := edgeWalk_wire_form data e
  exact ⟨j, by omega⟩

/-- The actual top connector alone has 48 edges, so every internal path has
a positive fourfold block count, as required by the endpoint inverse formula. -/
theorem internal_count_positive_wire_form {V E : Type*} {half : ℕ} (data : Data V E half) (e : E) :
    ∃ j : ℕ, 0 < j ∧ (edgeWalk data e).length - 1 = 4 * j := by
  obtain ⟨j, hj⟩ := edgeWalk_wire_form data e
  have hl : 48 ≤ (edgeWalk data e).length := by
    rw [edgeWalk_length]
    unfold Terminals.edgeLength
    omega
  exact ⟨j, by omega, by omega⟩

theorem embedding_box {V E : Type*} {half : ℕ} (data : Data V E half) (v : Vertex data) :
    InHorizontalBox (2 * half) (embedding data v) ∧
      -16 ≤ (embedding data v).2.2 ∧ (embedding data v).2.2 ≤ 96 * (2 * half) + 16 := by
  cases v with
  | inl v => exact Gluing.embedding_box data (Sum.inl (Sum.inl v))
  | inr v =>
    exact edgeWalk_box data v.1 (v.2.val + 1) (by have := v.2.isLt; omega)

/-- The actual coordinates in the complete occupancy array. -/
noncomputable def boxIndex {V E : Type*} {half : ℕ} (data : Data V E half) (v : Vertex data) :
    Fin (boxSideXY (2 * half)) × Fin (boxSideXY (2 * half)) × Fin (boxSideZ (2 * half)) :=
  let p := embedding data v
  (⟨(p.1 + 4).toNat, by have h := embedding_box data v; unfold InHorizontalBox at h; unfold boxSideXY; dsimp only [p]; omega⟩,
   ⟨(p.2.1 + 4).toNat, by have h := embedding_box data v; unfold InHorizontalBox at h; unfold boxSideXY; dsimp only [p]; omega⟩,
   ⟨(p.2.2 + 16).toNat, by have h := embedding_box data v; unfold boxSideZ; dsimp only [p]; omega⟩)

theorem boxIndex_injective {V E : Type*} {half : ℕ} (data : Data V E half) :
    Function.Injective (boxIndex data) := by
  intro a b he
  have ha := embedding_box data a
  have hb := embedding_box data b
  have hx := congrArg (fun p => p.1.val) he
  have hy := congrArg (fun p => p.2.1.val) he
  have hz := congrArg (fun p => p.2.2.val) he
  simp only [boxIndex] at hx hy hz
  unfold InHorizontalBox at ha hb
  apply embedding_injective data
  apply Prod.ext
  · omega
  · apply Prod.ext <;> omega

noncomputable instance {V E : Type*} [Fintype V] [Fintype E] {half : ℕ} (data : Data V E half) :
    Fintype (Vertex data) := by unfold Vertex; infer_instance

/-- The occupied subdivision is bounded by the full ambient lattice box. -/
theorem vertex_card_le_box {V E : Type*} [Fintype V] [Fintype E] {half : ℕ}
    (data : Data V E half) : Fintype.card (Vertex data) ≤ boxSites (2 * half) := by
  have hh := Fintype.card_le_of_injective (boxIndex data) (boxIndex_injective data)
  simpa only [Fintype.card_prod, Fintype.card_fin, boxSites, pow_two, Nat.mul_assoc] using hh

/-- Exact vertex count of the graph subdivision actually constructed. -/
theorem vertex_card {V E : Type*} [Fintype V] [Fintype E] {half : ℕ} (data : Data V E half) :
    Fintype.card (Vertex data) = Fintype.card V + ∑ e : E, ((edgeWalk data e).length - 1) := by
  simp only [Vertex, Fintype.card_sum, Fintype.card_sigma, Fintype.card_fin]

end Maxwell.Logical.Routing.Subdivision
