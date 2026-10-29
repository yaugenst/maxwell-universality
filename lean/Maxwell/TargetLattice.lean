import Maxwell.TargetRowGeometry
import Maxwell.Spectral.Lattice
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Finite PEC geometry inside the infinite Yee lattice

Retained electric edges use their physical positive transverse coordinates.
Finite faces use their integer lower-corner coordinates. The finite vectors
embed by zero extension into the actual square-summable lattice field.
-/

namespace Maxwell.Target

noncomputable section

open scoped ComplexConjugate

def sequenceExtensionLinear {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (embedding : ι ↪ κ) : EuclideanSpace ℂ ι →ₗ[ℂ] Spectral.SequenceL2 κ where
  toFun x := ∑ i, lp.single 2 (embedding i) (x i)
  map_add' x y := by simp [lp.single_add, Finset.sum_add_distrib]
  map_smul' c x := by
    change (∑ i, lp.single (E := fun _ : κ => ℂ) 2 (embedding i) (c • x i)) =
      c • ∑ i, lp.single (E := fun _ : κ => ℂ) 2 (embedding i) (x i)
    simp only [lp.single_smul, Finset.smul_sum]

theorem sequenceExtensionLinear_apply {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (embedding : ι ↪ κ) (x : EuclideanSpace ℂ ι) (k : κ) :
    sequenceExtensionLinear embedding x k =
      ∑ i, if k = embedding i then x i else 0 := by
  change (∑ i, lp.single (E := fun _ : κ => ℂ) 2 (embedding i) (x i)) k = _
  simp only [lp.coeFn_sum, Finset.sum_apply, lp.single_apply, Pi.single_apply]

@[simp]
theorem sequenceExtensionLinear_at {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [DecidableEq κ] (embedding : ι ↪ κ) (x : EuclideanSpace ℂ ι) (i : ι) :
    sequenceExtensionLinear embedding x (embedding i) = x i := by
  rw [sequenceExtensionLinear_apply]
  simp only [embedding.injective.eq_iff]
  simp

theorem sequenceExtensionLinear_inner {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [DecidableEq κ] (embedding : ι ↪ κ) (x y : EuclideanSpace ℂ ι) :
    inner ℂ (sequenceExtensionLinear embedding x) (sequenceExtensionLinear embedding y) =
      inner ℂ x y := by
  change inner ℂ (∑ i, lp.single 2 (embedding i) (x i))
    (sequenceExtensionLinear embedding y) = inner ℂ x y
  simp only [sum_inner, lp.inner_single_left, sequenceExtensionLinear_at, PiLp.inner_apply]

/-- Zero extension along an injective finite index map is an isometry. -/
def sequenceExtension {ι κ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq κ]
    (embedding : ι ↪ κ) : EuclideanSpace ℂ ι →ₗᵢ[ℂ] Spectral.SequenceL2 κ :=
  (sequenceExtensionLinear embedding).isometryOfInner (sequenceExtensionLinear_inner embedding)

def sequenceRestriction {ι κ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq κ]
    (embedding : ι ↪ κ) : Spectral.SequenceL2 κ →L[ℂ] EuclideanSpace ℂ ι :=
  (sequenceExtension embedding).toContinuousLinearMap.adjoint

theorem sequenceExtension_norm_le {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [DecidableEq κ] (embedding : ι ↪ κ) :
    ‖(sequenceExtension embedding).toContinuousLinearMap‖ ≤ 1 :=
  (sequenceExtension embedding).norm_toContinuousLinearMap_le

theorem sequenceRestriction_norm_le {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [DecidableEq κ] (embedding : ι ↪ κ) : ‖sequenceRestriction embedding‖ ≤ 1 := by
  simpa [sequenceRestriction] using sequenceExtension_norm_le embedding

@[simp]
theorem sequenceExtension_single {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [DecidableEq κ] (embedding : ι ↪ κ) (i : ι) (z : ℂ) :
    sequenceExtension embedding (EuclideanSpace.single i z) = lp.single 2 (embedding i) z := by
  change (∑ j, lp.single (E := fun _ : κ => ℂ) 2 (embedding j) (EuclideanSpace.single i z j)) = _
  simp only [PiLp.single_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]
  · simp

@[simp]
theorem sequenceRestriction_apply {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [DecidableEq κ] (embedding : ι ↪ κ) (y : Spectral.SequenceL2 κ) (i : ι) :
    sequenceRestriction embedding y i = y (embedding i) := by
  have h := (sequenceExtension embedding).toContinuousLinearMap.adjoint_inner_right
    (EuclideanSpace.single i 1) y
  simpa [sequenceRestriction, EuclideanSpace.inner_single_left,
    sequenceExtension_single, lp.inner_single_left] using h

theorem sequenceRestriction_extension {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [DecidableEq κ] (embedding : ι ↪ κ) :
    (sequenceRestriction embedding).comp (sequenceExtension embedding).toContinuousLinearMap =
      ContinuousLinearMap.id ℂ (EuclideanSpace ℂ ι) := by
  ext x i
  change sequenceRestriction embedding (sequenceExtension embedding x) i = x i
  rw [sequenceRestriction_apply]
  exact sequenceExtensionLinear_at embedding x i

/-- Physical edge positions, including the `+1` transverse interior offsets. -/
def latticeEdge (B : Box) : B.Edge ↪ Spectral.Lattice.Edge where
  toFun
    | .inl (i, j, k) => (0, ![(i.val : ℤ), (j.val : ℤ) + 1, (k.val : ℤ) + 1])
    | .inr (.inl (i, j, k)) => (1, ![(i.val : ℤ) + 1, (j.val : ℤ), (k.val : ℤ) + 1])
    | .inr (.inr (i, j, k)) => (2, ![(i.val : ℤ) + 1, (j.val : ℤ) + 1, (k.val : ℤ)])
  inj' := by
    rintro (⟨i, j, k⟩ | (⟨i, j, k⟩ | ⟨i, j, k⟩))
      (⟨i', j', k'⟩ | (⟨i', j', k'⟩ | ⟨i', j', k'⟩)) h <;>
      simp_all [Fin.ext_iff, funext_iff, Fin.forall_fin_succ]

/-- Oriented face at its integer lower corner. -/
def latticeFace (B : Box) : B.Face ↪ Spectral.Lattice.Edge where
  toFun
    | .inl (i, j, k) => (0, ![(i.val : ℤ), (j.val : ℤ), (k.val : ℤ)])
    | .inr (.inl (i, j, k)) => (1, ![(i.val : ℤ), (j.val : ℤ), (k.val : ℤ)])
    | .inr (.inr (i, j, k)) => (2, ![(i.val : ℤ), (j.val : ℤ), (k.val : ℤ)])
  inj' := by
    rintro (⟨i, j, k⟩ | (⟨i, j, k⟩ | ⟨i, j, k⟩))
      (⟨i', j', k'⟩ | (⟨i', j', k'⟩ | ⟨i', j', k'⟩)) h <;>
      simp_all [Fin.ext_iff, funext_iff, Fin.forall_fin_succ]

@[simp] theorem latticeEdge_x (B : Box) (i : Fin B.nx) (j : Fin (B.ny - 1))
    (k : Fin (B.nz - 1)) : latticeEdge B (.inl (i, j, k)) =
      (0, ![(i.val : ℤ), (j.val : ℤ) + 1, (k.val : ℤ) + 1]) := rfl
@[simp] theorem latticeEdge_y (B : Box) (i : Fin (B.nx - 1)) (j : Fin B.ny)
    (k : Fin (B.nz - 1)) : latticeEdge B (.inr (.inl (i, j, k))) =
      (1, ![(i.val : ℤ) + 1, (j.val : ℤ), (k.val : ℤ) + 1]) := rfl
@[simp] theorem latticeEdge_z (B : Box) (i : Fin (B.nx - 1)) (j : Fin (B.ny - 1))
    (k : Fin B.nz) : latticeEdge B (.inr (.inr (i, j, k))) =
      (2, ![(i.val : ℤ) + 1, (j.val : ℤ) + 1, (k.val : ℤ)]) := rfl
@[simp] theorem latticeFace_x (B : Box) (i : Fin (B.nx + 1)) (j : Fin B.ny)
    (k : Fin B.nz) : latticeFace B (.inl (i, j, k)) =
      (0, ![(i.val : ℤ), (j.val : ℤ), (k.val : ℤ)]) := rfl
@[simp] theorem latticeFace_y (B : Box) (i : Fin B.nx) (j : Fin (B.ny + 1))
    (k : Fin B.nz) : latticeFace B (.inr (.inl (i, j, k))) =
      (1, ![(i.val : ℤ), (j.val : ℤ), (k.val : ℤ)]) := rfl
@[simp] theorem latticeFace_z (B : Box) (i : Fin B.nx) (j : Fin B.ny)
    (k : Fin (B.nz + 1)) : latticeFace B (.inr (.inr (i, j, k))) =
      (2, ![(i.val : ℤ), (j.val : ℤ), (k.val : ℤ)]) := rfl

@[simp] theorem site_sub_single_zero (i j k : ℤ) :
    ![i, j, k] - Pi.single (0 : Fin 3) 1 = ![i - 1, j, k] := by
  ext d; fin_cases d <;> simp
@[simp] theorem site_sub_single_one (i j k : ℤ) :
    ![i, j, k] - Pi.single (1 : Fin 3) 1 = ![i, j - 1, k] := by
  ext d; fin_cases d <;> simp
@[simp] theorem site_sub_single_two (i j k : ℤ) :
    ![i, j, k] - Pi.single (2 : Fin 3) 1 = ![i, j, k - 1] := by
  ext d; fin_cases d <;> simp

def edgeExtension (B : Box) : EuclideanSpace ℂ B.Edge →L[ℂ] Spectral.Lattice.Field :=
  (sequenceExtension (latticeEdge B)).toContinuousLinearMap

def faceExtension (B : Box) : EuclideanSpace ℂ B.Face →L[ℂ] Spectral.Lattice.Field :=
  (sequenceExtension (latticeFace B)).toContinuousLinearMap

def edgeRestriction (B : Box) : Spectral.Lattice.Field →L[ℂ] EuclideanSpace ℂ B.Edge :=
  sequenceRestriction (latticeEdge B)

def faceRestriction (B : Box) : Spectral.Lattice.Field →L[ℂ] EuclideanSpace ℂ B.Face :=
  sequenceRestriction (latticeFace B)

theorem edgeExtension_norm_le (B : Box) : ‖edgeExtension B‖ ≤ 1 :=
  sequenceExtension_norm_le (latticeEdge B)

theorem edgeRestriction_norm_le (B : Box) : ‖edgeRestriction B‖ ≤ 1 :=
  sequenceRestriction_norm_le (latticeEdge B)

theorem faceExtension_norm_le (B : Box) : ‖faceExtension B‖ ≤ 1 :=
  sequenceExtension_norm_le (latticeFace B)

theorem faceRestriction_norm_le (B : Box) : ‖faceRestriction B‖ ≤ 1 :=
  sequenceRestriction_norm_le (latticeFace B)

theorem edgeRestriction_extension (B : Box) :
    (edgeRestriction B).comp (edgeExtension B) =
      ContinuousLinearMap.id ℂ (EuclideanSpace ℂ B.Edge) :=
  sequenceRestriction_extension (latticeEdge B)

theorem fieldPullback_single (p : Equiv.Perm Spectral.Lattice.Edge)
    (k : Spectral.Lattice.Edge) (z : ℂ) :
    Spectral.Lattice.fieldPullback p (lp.single 2 k z) = lp.single 2 (p.symm k) z := by
  ext i
  simp [Spectral.Lattice.fieldPullback_apply, lp.single_apply, Pi.single_apply,
    ← Equiv.eq_symm_apply]

/-- Every nonzero infinite curl incidence of a retained edge is exactly one
of its four retained finite faces, with the same orientation. -/
theorem yeeCurl_single_retained {B : Box} (e : B.Edge) (z : ℂ) :
    Spectral.Lattice.yeeCurl (lp.single 2 (latticeEdge B e) z) =
      ∑ a : Fin 4, (incidenceSign a : ℂ) •
        lp.single 2 (latticeFace B (incidentFaces e a)) z := by
  simp only [Spectral.Lattice.yeeCurl, add_apply, sub_apply, fieldPullback_single]
  rcases e with (⟨i, j, k⟩ | (⟨i, j, k⟩ | ⟨i, j, k⟩)) <;>
    simp [incidentFaces, incidenceSign, Fin.sum_univ_succ,
      Spectral.Lattice.fieldPermutation, Spectral.Lattice.directionCycle,
      Spectral.Lattice.unitSite, interiorVertex, interiorLower, interiorUpper,
      Matrix.vecHead, Matrix.vecTail] <;> abel

/-- The rectangular finite curl acting between Euclidean edge and face fields. -/
def finiteCurl (B : Box) : EuclideanSpace ℂ B.Edge →L[ℂ] EuclideanSpace ℂ B.Face :=
  (Matrix.toEuclideanLin ((curl B).map fun q => (q : ℂ))).toContinuousLinearMap

theorem finiteCurl_apply (B : Box) (x : EuclideanSpace ℂ B.Edge) (f : B.Face) :
    finiteCurl B x f = ∑ e, (curl B f e : ℂ) * x e := rfl

theorem finiteCurl_single {B : Box} (e : B.Edge) (z : ℂ) :
    finiteCurl B (EuclideanSpace.single e z) =
      ∑ a : Fin 4, (incidenceSign a : ℂ) • EuclideanSpace.single (incidentFaces e a) z := by
  ext f
  simp [finiteCurl_apply, PiLp.single_apply, curl, Rat.cast_sum,
    Finset.sum_mul, apply_ite, ite_mul, Pi.single_apply]

/-- Exact intertwining with the full infinite-lattice curl. All infinite
curl output lies on the enumerated finite faces, not just its restriction. -/
theorem yeeCurl_extension (B : Box) :
    Spectral.Lattice.yeeCurl.comp (edgeExtension B) =
      (faceExtension B).comp (finiteCurl B) := by
  have hs (e : B.Edge) (z : ℂ) :
      Spectral.Lattice.yeeCurl (edgeExtension B (EuclideanSpace.single e z)) =
        faceExtension B (finiteCurl B (EuclideanSpace.single e z)) := by
    rw [finiteCurl_single]
    simp only [map_sum, map_smul]
    change Spectral.Lattice.yeeCurl
      (sequenceExtension (latticeEdge B) (EuclideanSpace.single e z)) = _
    rw [sequenceExtension_single, yeeCurl_single_retained]
    apply Finset.sum_congr rfl
    intro a _
    rw [faceExtension]
    change _ = (incidenceSign a : ℂ) •
      sequenceExtension (latticeFace B) (EuclideanSpace.single (incidentFaces e a) z)
    rw [sequenceExtension_single]
  apply ContinuousLinearMap.ext
  intro x
  have hx : x = ∑ e : B.Edge, EuclideanSpace.single e (x e) := by
    ext e
    simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.single_apply,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  change Spectral.Lattice.yeeCurl (edgeExtension B x) = faceExtension B (finiteCurl B x)
  conv_lhs => rw [hx]
  conv_rhs => rw [hx]
  simp only [map_sum, hs]

/-- Exact principal compression of infinite curl energy. -/
theorem curl_gram_compression (B : Box) :
    (edgeRestriction B).comp
      (Spectral.Lattice.yeeCurl.adjoint.comp
        (Spectral.Lattice.yeeCurl.comp (edgeExtension B))) =
      (finiteCurl B).adjoint.comp (finiteCurl B) := by
  have h := congrArg ContinuousLinearMap.adjoint (yeeCurl_extension B)
  simp only [ContinuousLinearMap.adjoint_comp] at h
  change (edgeExtension B).adjoint.comp
    (Spectral.Lattice.yeeCurl.adjoint.comp
      (Spectral.Lattice.yeeCurl.comp (edgeExtension B))) = _
  rw [← ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.comp_assoc, h]
  rw [ContinuousLinearMap.comp_assoc, yeeCurl_extension]
  have hf : (faceExtension B).adjoint.comp (faceExtension B) =
      ContinuousLinearMap.id ℂ (EuclideanSpace ℂ B.Face) :=
    sequenceRestriction_extension (latticeFace B)
  simp only [ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.comp_assoc
    (faceExtension B).adjoint (faceExtension B) (finiteCurl B), hf,
    ContinuousLinearMap.id_comp]

theorem finiteCurl_gram_matrix (B : Box) :
    (finiteCurl B).adjoint.comp (finiteCurl B) =
      Matrix.toEuclideanCLM (n := B.Edge) (𝕜 := ℂ)
        (((curl B).transpose * curl B).map fun q => (q : ℂ)) := by
  let C : Matrix B.Face B.Edge ℂ := (curl B).map fun q => (q : ℂ)
  have hm : C.conjTranspose * C =
      ((curl B).transpose * curl B).map (fun q => (q : ℂ)) := by
    ext i j
    simp [C, Matrix.mul_apply, Matrix.conjTranspose_apply, Rat.cast_sum, Rat.cast_mul]
  apply ContinuousLinearMap.ext
  intro x
  change (Matrix.toEuclideanLin C).toContinuousLinearMap.adjoint
    ((Matrix.toEuclideanLin C).toContinuousLinearMap x) = _
  rw [← LinearMap.adjoint_toContinuousLinearMap,
    ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  change ((Matrix.toEuclideanLin C.conjTranspose).comp (Matrix.toEuclideanLin C)) x = _
  rw [← Matrix.toLpLin_mul 2 2 2, hm]
  rfl

/-- The finite rational curl Gram matrix, cast to the physical complex
field, is exactly a principal compression of the infinite Yee operator. -/
theorem curl_matrix_compression (B : Box) :
    (edgeRestriction B).comp
      (Spectral.Lattice.yeeCurl.adjoint.comp
        (Spectral.Lattice.yeeCurl.comp (edgeExtension B))) =
      Matrix.toEuclideanCLM (n := B.Edge) (𝕜 := ℂ)
        (((curl B).transpose * curl B).map fun q => (q : ℂ)) := by
  rw [curl_gram_compression, finiteCurl_gram_matrix]

def latticeCell {B : Box} (c : B.Cell) : Spectral.Lattice.Site :=
  ![(c.1.val : ℤ), (c.2.1.val : ℤ), (c.2.2.val : ℤ)]

/-- Four physical cells touching an infinite electric edge, in the same
coordinate order used by the finite scalar-cell interface. -/
def latticeIncidentCells (e : Spectral.Lattice.Edge) : Fin 4 → Spectral.Lattice.Site :=
  let p := e.2
  ![![![p 0, p 1 - 1, p 2 - 1], ![p 0, p 1, p 2 - 1],
       ![p 0, p 1 - 1, p 2], ![p 0, p 1, p 2]],
    ![![p 0 - 1, p 1, p 2 - 1], ![p 0, p 1, p 2 - 1],
       ![p 0 - 1, p 1, p 2], ![p 0, p 1, p 2]],
    ![![p 0 - 1, p 1 - 1, p 2], ![p 0, p 1 - 1, p 2],
       ![p 0 - 1, p 1, p 2], ![p 0, p 1, p 2]]] e.1

theorem lattice_incidentCells {B : Box} (e : B.Edge) (a : Fin 4) :
    latticeIncidentCells (latticeEdge B e) a = latticeCell (incidentCells e a) := by
  rcases e with (⟨i, j, k⟩ | (⟨i, j, k⟩ | ⟨i, j, k⟩)) <;>
    fin_cases a <;>
    simp [latticeIncidentCells, latticeCell, incidentCells, interiorLower, interiorUpper]

def latticeEdgeAverage (m : Spectral.Lattice.Site → ℝ) (e : Spectral.Lattice.Edge) : ℝ :=
  (m (latticeIncidentCells e 0) + m (latticeIncidentCells e 1) +
    m (latticeIncidentCells e 2) + m (latticeIncidentCells e 3)) / 4

/-- Restricting a scalar lattice material to the box gives exactly the
finite four-cell mass diagonal, including retained edges next to PEC walls. -/
theorem latticeEdgeAverage_restriction {B : Box}
    (material : ScalarMaterial B.nx B.ny B.nz) (m : Spectral.Lattice.Site → ℝ)
    (hm : ∀ c : B.Cell, m (latticeCell c) = (material.value c : ℝ)) (e : B.Edge) :
    latticeEdgeAverage m (latticeEdge B e) = (edgeAverage material.value e : ℝ) := by
  simp [latticeEdgeAverage, lattice_incidentCells, hm, edgeAverage]

theorem material_matrix_compression {B : Box}
    (material : ScalarMaterial B.nx B.ny B.nz) (m : Spectral.Lattice.Edge → ℝ)
    (K : ℝ) (hK : 0 ≤ K) (hm : ∀ i, |m i| ≤ K)
    (hmatch : ∀ e : B.Edge, m (latticeEdge B e) = (edgeAverage material.value e : ℝ)) :
    (edgeRestriction B).comp
      ((Spectral.realSequenceMultiplier m K hK hm).comp (edgeExtension B)) =
      Matrix.toEuclideanCLM (n := B.Edge) (𝕜 := ℂ)
        ((Matrix.diagonal (edgeAverage material.value)).map fun q => (q : ℂ)) := by
  apply ContinuousLinearMap.ext
  intro x
  ext e
  change sequenceRestriction (latticeEdge B)
    (Spectral.realSequenceMultiplier m K hK hm (edgeExtension B x)) e = _
  rw [sequenceRestriction_apply, Spectral.realSequenceMultiplier_apply, hmatch]
  change ((edgeAverage material.value e : ℝ) : ℂ) *
    sequenceExtensionLinear (latticeEdge B) x (latticeEdge B e) =
    ∑ j, ((Matrix.diagonal (edgeAverage material.value)) e j : ℂ) * x j
  rw [sequenceExtensionLinear_at]
  rw [Finset.sum_eq_single e]
  · simp
  · intro j _ hje
    simp [Ne.symm hje]
  · simp

/-- The full finite PEC scalar Maxwell matrix is the exact principal
compression of the infinite electric operator whenever their physical
edge material averages agree. No spectral or boundary-gap hypothesis is used. -/
theorem maxwell_matrix_compression {B : Box}
    (material : ScalarMaterial B.nx B.ny B.nz) (m : Spectral.Lattice.Edge → ℝ)
    (K : ℝ) (hK : 0 ≤ K) (hm : ∀ i, |m i| ≤ K)
    (hmatch : ∀ e : B.Edge, m (latticeEdge B e) = (edgeAverage material.value e : ℝ)) :
    (edgeRestriction B).comp
      ((Spectral.Lattice.electricOperator m K hK hm).comp (edgeExtension B)) =
      Matrix.toEuclideanCLM (n := B.Edge) (𝕜 := ℂ)
        ((maxwell material).map fun q => (q : ℂ)) := by
  have hc := curl_matrix_compression B
  have hd := material_matrix_compression material m K hK hm hmatch
  apply ContinuousLinearMap.ext
  intro x
  ext e
  have hcx := congrArg (fun T : EuclideanSpace ℂ B.Edge →L[ℂ] EuclideanSpace ℂ B.Edge =>
    T x e) hc
  have hdx := congrArg (fun T : EuclideanSpace ℂ B.Edge →L[ℂ] EuclideanSpace ℂ B.Edge =>
    T x e) hd
  simp only [ContinuousLinearMap.comp_apply] at hcx hdx
  simp only [ContinuousLinearMap.comp_apply, Spectral.Lattice.electricOperator,
    sub_apply, smul_apply, map_sub, map_smul]
  change edgeRestriction B (Spectral.Lattice.yeeCurl.adjoint
      (Spectral.Lattice.yeeCurl (edgeExtension B x))) e -
    (1 / 64 : ℂ) * edgeRestriction B
      (Spectral.realSequenceMultiplier m K hK hm (edgeExtension B x)) e = _
  rw [hcx, hdx]
  change (∑ j, (((curl B).transpose * curl B) e j : ℂ) * x j) -
    (1 / 64 : ℂ) * (∑ j, ((Matrix.diagonal (edgeAverage material.value)) e j : ℂ) * x j) =
      ∑ j, (maxwell material e j : ℂ) * x j
  simp only [maxwell, operator, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  push_cast
  simp only [sub_mul, Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc]

/-- Scalar-cell specialization: agreeing on the physical cells is sufficient
for the exact finite/infinite full Maxwell operator identity. -/
theorem scalar_maxwell_matrix_compression {B : Box}
    (material : ScalarMaterial B.nx B.ny B.nz) (m : Spectral.Lattice.Site → ℝ)
    (hcell : ∀ c : B.Cell, m (latticeCell c) = (material.value c : ℝ))
    (K : ℝ) (hK : 0 ≤ K) (hm : ∀ i, |latticeEdgeAverage m i| ≤ K) :
    (edgeRestriction B).comp
      ((Spectral.Lattice.electricOperator (latticeEdgeAverage m) K hK hm).comp
        (edgeExtension B)) =
      Matrix.toEuclideanCLM (n := B.Edge) (𝕜 := ℂ)
        ((maxwell material).map fun q => (q : ℂ)) :=
  maxwell_matrix_compression material (latticeEdgeAverage m) K hK hm
    (latticeEdgeAverage_restriction material m hcell)

end

end Maxwell.Target
