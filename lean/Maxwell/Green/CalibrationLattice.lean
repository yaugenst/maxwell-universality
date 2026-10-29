import Maxwell.Green.CouplingCalibration
import Maxwell.Cost.CalibrationMatrix.Value

/-! A finite dense rational matrix executes exactly the local Yee stencil
on the containing support cube. The matrix is generated from the same
explicit rational stencil used in the physical inverse approximation. -/
namespace Maxwell.Defect.FiniteStencil
open Spectral Spectral.Lattice
open scoped Matrix
set_option maxHeartbeats 600000
variable {n : ℕ}

def coefficients (edges : Fin n → Edge) (v : SparseField) : Fin n → ℚ :=
  fun i => evaluate v (edges i)

def stencilMatrix (edges : Fin n → Edge) (m : Edge → ℚ) (z : ℚ) :
    Matrix (Fin n) (Fin n) ℚ :=
  fun i j => evaluate (step m z [(edges j, 1)]) (edges i)

theorem embed_reconstruction (edges : Fin n ↪ Edge) (v : SparseField)
    (hs : ∀ t ∈ v, t.1 ∈ Set.range edges) :
    embed (rationalSource edges (coefficients edges v)) = embed v := by
  rw [embed_rationalSource]
  ext e
  change Target.sequenceExtensionLinear edges
    (WithLp.toLp 2 (fun i => (coefficients edges v i : ℂ))) e = embed v e
  by_cases he : e ∈ Set.range edges
  · obtain ⟨i, rfl⟩ := he
    rw [Target.sequenceExtensionLinear_at, embed_apply]
    rfl
  · rw [Target.sequenceExtensionLinear_apply, embed_apply]
    have hz : evaluate v e = 0 := evaluate_eq_zero_of_not_mem v e (by
      intro h
      obtain ⟨t, ht, hte⟩ := List.mem_map.mp h
      exact he (hte ▸ hs t ht))
    rw [hz, Rat.cast_zero]
    apply Finset.sum_eq_zero
    intro i _
    simp [show e ≠ edges i from fun h => he ⟨i, h.symm⟩]

theorem stencilMatrix_mulVec (edges : Fin n ↪ Edge) (m : Edge → ℚ)
    (K : ℝ) (hK : 0 ≤ K) (hm : ∀ e, |(m e : ℝ)| ≤ K)
    (z : ℚ) (a : Fin n → ℚ) (i : Fin n) :
    coefficients edges (step m z (rationalSource edges a)) i =
      (stencilMatrix edges m z *ᵥ a) i := by
  apply Rat.cast_injective (α := ℂ)
  change (evaluate (step m z (rationalSource edges a)) (edges i) : ℂ) = _
  rw [← embed_apply, embed_step m K hK hm, embed_rationalSource]
  change operator m K hK hm z (∑ j, lp.single 2 (edges j) (a j : ℂ)) (edges i) = _
  rw [map_sum]
  simp only [lp.coeFn_sum, Finset.sum_apply, Matrix.mulVec, dotProduct,
    Rat.cast_sum, Rat.cast_mul]
  apply Finset.sum_congr rfl
  intro j _
  have hs : lp.single (E := fun _ : Edge => ℂ) 2 (edges j) (a j : ℂ) =
      (a j : ℂ) • embed [(edges j, 1)] := by
    simp only [embed_cons, embed_nil, Rat.cast_one, add_zero, ← lp.single_smul]
    simp
  rw [hs, map_smul]
  change (a j : ℂ) * operator m K hK hm z (embed [(edges j, 1)]) (edges i) = _
  rw [← embed_step m K hK hm, embed_apply]
  change _ = (evaluate (step m z [(edges j, 1)]) (edges i) : ℂ) * (a j : ℂ)
  ring

theorem coefficients_step (edges : Fin n ↪ Edge) (m : Edge → ℚ)
    (K : ℝ) (hK : 0 ≤ K) (hm : ∀ e, |(m e : ℝ)| ≤ K)
    (z : ℚ) (v : SparseField) (hs : ∀ t ∈ v, t.1 ∈ Set.range edges) :
    coefficients edges (step m z v) = stencilMatrix edges m z *ᵥ coefficients edges v := by
  funext i
  rw [← stencilMatrix_mulVec edges m K hK hm]
  apply Rat.cast_injective (α := ℂ)
  change (evaluate (step m z v) (edges i) : ℂ) =
    (evaluate (step m z (rationalSource edges (coefficients edges v))) (edges i) : ℂ)
  rw [← embed_apply, ← embed_apply, embed_step m K hK hm, embed_step m K hK hm,
    embed_reconstruction edges v hs]

@[simp] theorem coefficients_compact (edges : Fin n → Edge) (v : SparseField) :
    coefficients edges (compact v) = coefficients edges v := by
  funext i
  exact evaluate_compact v (edges i)

@[simp] theorem coefficients_append (edges : Fin n → Edge) (u v : SparseField) :
    coefficients edges (u ++ v) = coefficients edges u + coefficients edges v := by
  funext i
  simp [coefficients, evaluate]

@[simp] theorem coefficients_scale (edges : Fin n → Edge) (q : ℚ) (v : SparseField) :
    coefficients edges (scale q v) = q • coefficients edges v := by
  funext i
  apply Rat.cast_injective (α := ℂ)
  change (evaluate (scale q v) (edges i) : ℂ) = ((q * evaluate v (edges i) : ℚ) : ℂ)
  rw [← embed_apply, embed_scale]
  simp [embed_apply]

/-- Rational Horner loop on one finite containing box. -/
def denseHorner (A : Matrix (Fin n) (Fin n) ℚ) (s : ℚ) (v : Fin n → ℚ) : ℕ → Fin n → ℚ
  | 0 => v
  | N+1 => v + denseHorner A s v N - s • (A *ᵥ (A *ᵥ denseHorner A s v N))

def denseInverse (A : Matrix (Fin n) (Fin n) ℚ) (s : ℚ) (v : Fin n → ℚ) (N : ℕ) : Fin n → ℚ :=
  s • (A *ᵥ denseHorner A s v N)
 
/-- A finite index set covers the entire propagation cube. -/
def Covers (edges : Fin n → Edge) (R : ℕ) : Prop :=
  ∀ e, (∀ j : Direction, |e.2 j| ≤ (R : ℤ)) → e ∈ Set.range edges

theorem Covers.mono {edges : Fin n → Edge} {R S : ℕ}
    (h : Covers edges S) (hRS : R ≤ S) : Covers edges R := by
  intro e he
  apply h e
  intro j
  exact (he j).trans (by exact_mod_cast hRS)

theorem Supported.in_cover {edges : Fin n → Edge} {R : ℕ} {v : SparseField}
    (hv : Supported v R) (hc : Covers edges R) : ∀ t ∈ v, t.1 ∈ Set.range edges :=
  fun t ht => hc t.1 (hv t ht)

theorem coefficients_horner (edges : Fin n ↪ Edge) (m : Edge → ℚ)
    (K : ℝ) (hK : 0 ≤ K) (hm : ∀ e, |(m e : ℝ)| ≤ K)
    (z s : ℚ) (v : SparseField) (R : ℕ) (hv : Supported v R) (N : ℕ)
    (hc : Covers edges (R+4*N)) :
    coefficients edges (hornerAction m z s N v) =
      denseHorner (stencilMatrix edges m z) s (coefficients edges v) N := by
  induction N with
  | zero => simp [hornerAction, denseHorner]
  | succ N ih =>
    have hc0 : Covers edges (R+4*N) := hc.mono (by omega)
    have hc1 : Covers edges (R+4*N+2) := hc.mono (by omega)
    have hs0 := (hv.hornerAction m z s N).in_cover hc0
    have hs1 := ((hv.hornerAction m z s N).step m z).in_cover hc1
    rw [hornerAction, coefficients_compact, coefficients_append, contractionStep,
      coefficients_append, coefficients_scale,
      coefficients_step edges m K hK hm z _ hs1,
      coefficients_step edges m K hK hm z _ hs0, ih hc0]
    ext i
    simp only [denseHorner, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      neg_mul]
    ring

theorem coefficients_inverse (edges : Fin n ↪ Edge) (m : Edge → ℚ)
    (K : ℝ) (hK : 0 ≤ K) (hm : ∀ e, |(m e : ℝ)| ≤ K)
    (z s : ℚ) (v : SparseField) (R : ℕ) (hv : Supported v R) (N : ℕ)
    (hc : Covers edges (R+4*N+2)) :
    coefficients edges (compactInverseAction m z s N v) =
      denseInverse (stencilMatrix edges m z) s (coefficients edges v) N := by
  have hc0 : Covers edges (R+4*N) := hc.mono (by omega)
  rw [compactInverseAction, coefficients_compact, coefficients_scale,
    coefficients_step edges m K hK hm z _ ((hv.hornerAction m z s N).in_cover hc0),
    coefficients_horner edges m K hK hm z s v R hv N hc0]
  rfl

def cubeEdges (R : ℕ) : Finset Edge := Finset.univ ×ˢ Maxwell.Green.integerCube R

private abbrev edgeOrder : LinearOrder Edge :=
  LinearOrder.lift' Encodable.encode Encodable.encode_injective

def cubeEmbedding (R : ℕ) : Fin (cubeEdges R).card ↪ Edge := by
  letI := edgeOrder
  exact ((cubeEdges R).orderEmbOfFin rfl).toEmbedding

theorem range_cubeEmbedding (R : ℕ) :
    Set.range (cubeEmbedding R) = (cubeEdges R : Set Edge) := by
  let := edgeOrder
  exact (cubeEdges R).range_orderEmbOfFin rfl

theorem cubeEmbedding_covers (R : ℕ) : Covers (cubeEmbedding R) R := by
  intro e he
  rw [range_cubeEmbedding]
  exact Finset.mem_product.mpr ⟨Finset.mem_univ _, (Maxwell.Green.mem_integerCube R _).mpr he⟩

theorem cubeEdges_card (R : ℕ) : (cubeEdges R).card = 3*(2*R+1)^3 := by
  simp only [cubeEdges, Finset.card_product, Finset.card_univ, Fintype.card_fin,
    Maxwell.Green.card_integerCube]

/-- Exact physical semantic binding of the dense finite algorithm; the
containing cube includes all intermediate support, so no boundary term is lost. -/
theorem denseInverse_physical (m : Edge → ℚ) (K : ℝ) (hK : 0 ≤ K)
    (hm : ∀ e, |(m e : ℝ)| ≤ K) (z s : ℚ) (v : SparseField)
    (R : ℕ) (hv : Supported v R) (N : ℕ) :
    embed (rationalSource (cubeEmbedding (R+4*N+2))
      (denseInverse (stencilMatrix (cubeEmbedding (R+4*N+2)) m z) s
        (coefficients (cubeEmbedding (R+4*N+2)) v) N)) =
      inversePolynomial (operator m K hK hm z) (s : ℂ) N (embed v) := by
  rw [← coefficients_inverse (cubeEmbedding (R+4*N+2)) m K hK hm z s v R hv N
    (cubeEmbedding_covers _), embed_reconstruction]
  · exact embed_compactInverseAction m K hK hm z s N v
  · exact (((hv.hornerAction m z s N).step m z).scale s).compact.in_cover
      (cubeEmbedding_covers _)

end Maxwell.Defect.FiniteStencil
