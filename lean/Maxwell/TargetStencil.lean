import Maxwell.TargetRowGeometry

/-! Executable relative-PEC stencil access. Boundary deletion uses only
coordinate comparisons; a curl Gram row needs sixteen retained-edge reads. -/
namespace Maxwell.Target
open Matrix
open scoped BigOperators
set_option maxHeartbeats 1000000

/-- Recover a retained edge from its physical coordinate, deleting exactly
those full edges tangent to the PEC boundary. -/
def retain {B : Box} : B.FullEdge → Option B.Edge
  | .inl (i,j,k) =>
    if h : 0 < j.val ∧ j.val < B.ny ∧ 0 < k.val ∧ k.val < B.nz then
      some (.inl (i,⟨j.val-1,by omega⟩,⟨k.val-1,by omega⟩)) else none
  | .inr (.inl (i,j,k)) =>
    if h : 0 < i.val ∧ i.val < B.nx ∧ 0 < k.val ∧ k.val < B.nz then
      some (.inr (.inl (⟨i.val-1,by omega⟩,j,⟨k.val-1,by omega⟩))) else none
  | .inr (.inr (i,j,k)) =>
    if h : 0 < i.val ∧ i.val < B.nx ∧ 0 < j.val ∧ j.val < B.ny then
      some (.inr (.inr (⟨i.val-1,by omega⟩,⟨j.val-1,by omega⟩,k))) else none

@[simp] theorem retain_fullEdge {B : Box} (e : B.Edge) : retain (fullEdge e) = some e := by
  rcases e with (⟨i,j,k⟩ | (⟨i,j,k⟩ | ⟨i,j,k⟩)) <;>
    have hi := i.isLt <;> have hj := j.isLt <;> have hk := k.isLt <;>
    simp [fullEdge,retain,interiorVertex] <;> omega

theorem fullEdge_of_retain {B : Box} (e : B.FullEdge) (r : B.Edge)
    (h : retain e = some r) : fullEdge r = e := by
  rcases e with (⟨i,j,k⟩ | (⟨i,j,k⟩ | ⟨i,j,k⟩)) <;>
    simp only [retain] at h <;> split_ifs at h <;> cases h <;>
    simp [fullEdge,interiorVertex,Fin.ext_iff] <;> omega

@[simp] theorem retain_eq_some_iff {B : Box} (e : B.FullEdge) (r : B.Edge) :
    retain e = some r ↔ fullEdge r = e :=
  ⟨fullEdge_of_retain e r,fun h => by rw [←h,retain_fullEdge]⟩

def retainedValue {B : Box} (v : B.Edge → ℚ) (e : B.FullEdge) : ℚ :=
  (retain e).elim 0 v

theorem retainedValue_eq_sum {B : Box} (v : B.Edge → ℚ) (e : B.FullEdge) :
    retainedValue v e = ∑ r : B.Edge, if fullEdge r = e then v r else 0 := by
  classical
  cases he : retain e with
  | none =>
    have hn (r : B.Edge) : fullEdge r ≠ e := by
      intro hr
      have hh := (retain_eq_some_iff e r).mpr hr
      rw [he] at hh
      cases hh
    simp [retainedValue,he,hn]
  | some r =>
    have hr := fullEdge_of_retain e r he
    have hh (s : B.Edge) : fullEdge s = e ↔ s = r := by
      rw [←hr]
      exact fullEdge_injective.eq_iff
    simp [retainedValue,he,hh]

/-- Exactly four coordinate lookups implement a forward curl row. -/
theorem curl_mulVec_stencil {B : Box} (v : B.Edge → ℚ) (f : B.Face) :
    (curl B *ᵥ v) f =
      ∑ b : Fin 4, incidenceSign b * retainedValue v (boundaryEdges f b) := by
  classical
  simp only [Matrix.mulVec,dotProduct,curl_row_formula,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [retainedValue_eq_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  split_ifs <;> simp_all

/-- Exactly four face lookups implement the transpose curl row. -/
theorem curl_transpose_mulVec_stencil {B : Box} (v : B.Face → ℚ) (e : B.Edge) :
    ((curl B).transpose *ᵥ v) e =
      ∑ a : Fin 4, incidenceSign a * v (incidentFaces e a) := by
  classical
  simp only [Matrix.mulVec,dotProduct,Matrix.transpose_apply,curl,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp only [ite_mul,zero_mul]
  simp

/-- The complete raw scalar-cell Maxwell row is a fixed sixteen-read curl
stencil plus its scalar mass term, including at every PEC boundary. -/
theorem operator_mulVec_stencil {B : Box} (material : B.Cell → ℚ)
    (v : B.Edge → ℚ) (e : B.Edge) :
    (operator B material *ᵥ v) e =
      (∑ a : Fin 4, ∑ b : Fin 4,
        incidenceSign a * incidenceSign b *
          retainedValue v (boundaryEdges (incidentFaces e a) b)) -
        (1/64 : ℚ)*edgeAverage material e*v e := by
  rw [operator,Matrix.sub_mulVec,←Matrix.mulVec_mulVec,
    Pi.sub_apply,curl_transpose_mulVec_stencil]
  simp only [curl_mulVec_stencil,Finset.mul_sum,mul_assoc,
    Matrix.smul_mulVec,Matrix.mulVec_diagonal,Pi.smul_apply,smul_eq_mul]

end Maxwell.Target
