import Maxwell.Spectral.ConventionalReality
import Maxwell.Spectral.Concrete
import Maxwell.Defect.RealCompression
import Mathlib.Algebra.BigOperators.Fin

/-! Exact rational conventional Yee fibers at time-reversal invariant momenta.
The finite checker matrix is a computable reindexing of the actual stencil. -/
namespace Maxwell.Spectral.ConventionalRational

open Maxwell.Spectral.PeriodicYee

def boundaryPhase (k : Direction → ℤ) (j : Direction) (r : Cell20) : ℚ :=
  if r j = 19 then (-1 : ℚ) ^ (k j) else 1

def difference (k : Direction → ℤ) (j : Direction) : Matrix Cell20 Cell20 ℚ :=
  fun r s => (if s = forwardCell j r then boundaryPhase k j r else 0) -
    (if s = r then 1 else 0)

def curl (k : Direction → ℤ) : Matrix Face20 Electric20 ℚ := fun i j =>
  if i.1 = 0 then
    if j.1 = 2 then difference k 1 i.2 j.2
    else if j.1 = 1 then -difference k 2 i.2 j.2 else 0
  else if i.1 = 1 then
    if j.1 = 0 then difference k 2 i.2 j.2
    else if j.1 = 2 then -difference k 0 i.2 j.2 else 0
  else
    if j.1 = 1 then difference k 0 i.2 j.2
    else if j.1 = 0 then -difference k 1 i.2 j.2 else 0

def edgeAverage (material : Cell20 → ℚ) (e : Electric20) : ℚ :=
  let p := transverseDirections e.1
  (material e.2 + material (e.2 - unitCell p.1) +
    material (e.2 - unitCell p.2) + material (e.2 - unitCell p.1 - unitCell p.2)) / 4

def mass (material : Cell20 → ℚ) : Matrix Electric20 Electric20 ℚ :=
  Matrix.diagonal (edgeAverage material)

def fiber (material : Cell20 → ℚ) (k : Direction → ℤ) : Matrix Electric20 Electric20 ℚ :=
  (curl k).transpose * curl k - (1/64 : ℚ) • mass material

theorem boundaryPhase_cast (k : Direction → ℤ) (j : Direction) (r : Cell20) :
    (boundaryPhase k j r : ℂ) = PeriodicYee.boundaryPhase (ConventionalAnalytic.trim k) j r := by
  unfold boundaryPhase PeriodicYee.boundaryPhase
  split_ifs <;> simp [ConventionalAnalytic.trim_exp]

theorem difference_cast (k : Direction → ℤ) (j : Direction) (r s : Cell20) :
    (difference k j r s : ℂ) = PeriodicYee.difference (ConventionalAnalytic.trim k) j r s := by
  unfold difference PeriodicYee.difference
  split_ifs <;> simp [boundaryPhase_cast]

theorem curl_cast (k : Direction → ℤ) :
    (curl k).map ((↑) : ℚ → ℂ) = PeriodicYee.curl (ConventionalAnalytic.trim k) := by
  ext i j
  change (curl k i j : ℂ) = _
  unfold curl PeriodicYee.curl
  split_ifs <;> simp [difference_cast]

theorem edgeAverage_cast (material : Cell20 → ℚ) (e : Electric20) :
    (edgeAverage material e : ℝ) = PeriodicYee.edgeAverage (fun r => (material r : ℝ)) e := by
  simp [edgeAverage, PeriodicYee.edgeAverage]

theorem mass_cast (material : Cell20 → ℚ) :
    (mass material).map ((↑) : ℚ → ℂ) = PeriodicYee.mass (fun r => (material r : ℝ)) := by
  ext i j
  by_cases h : i = j
  · subst j
    simp [mass, PeriodicYee.mass, ← edgeAverage_cast]
  · simp [mass, PeriodicYee.mass, h]

private theorem rational_map_transpose {ι κ : Type*} (M : Matrix ι κ ℚ) :
    M.transpose.map ((↑) : ℚ → ℂ) = (M.map ((↑) : ℚ → ℂ)).conjTranspose := by
  ext i j
  simp

private theorem rational_map_smul {ι κ : Type*} (M : Matrix ι κ ℚ) (a : ℚ) :
    (a • M).map ((↑) : ℚ → ℂ) = (a : ℂ) • M.map ((↑) : ℚ → ℂ) := by
  ext i j
  simp

private theorem rational_map_mul {ι κ ν : Type*} [Fintype κ]
    (A : Matrix ι κ ℚ) (B : Matrix κ ν ℚ) :
    (A * B).map ((↑) : ℚ → ℂ) = A.map ((↑) : ℚ → ℂ) * B.map ((↑) : ℚ → ℂ) := by
  ext i j
  simp [Matrix.mul_apply]

private theorem rational_map_sub {ι κ : Type*} (A B : Matrix ι κ ℚ) :
    (A - B).map ((↑) : ℚ → ℂ) = A.map ((↑) : ℚ → ℂ) - B.map ((↑) : ℚ → ℂ) := by
  ext i j
  simp

/-- Entrywise casting the rational TRIM fiber gives the actual complex
conventional fiber, including the four-cell edge mass average. -/
theorem fiber_cast (material : Cell20 → ℚ) (k : Direction → ℤ) :
    (fiber material k).map ((↑) : ℚ → ℂ) =
      PeriodicYee.fiber (fun r => (material r : ℝ)) (ConventionalAnalytic.trim k) := by
  unfold fiber PeriodicYee.fiber
  rw [rational_map_sub, rational_map_mul, rational_map_transpose, rational_map_smul,
    curl_cast, mass_cast]
  norm_num

theorem fiber_symmetric (material : Cell20 → ℚ) (k : Direction → ℤ) :
    (fiber material k).IsSymm := by
  change (fiber material k).transpose = fiber material k
  simp [fiber, mass, Matrix.transpose_mul]

/-- The literal frozen scalar cell table, before extension to real scalars. -/
def concreteMaterial (r : Cell20) : ℚ :=
  Maxwell.Certificate.Material.cellValue (Concrete.cellCoordinate r)

theorem concreteMaterial_cast (r : Cell20) : (concreteMaterial r : ℝ) = Concrete.material r := rfl

theorem concrete_fiber_cast (k : Direction → ℤ) :
    (fiber concreteMaterial k).map ((↑) : ℚ → ℂ) =
      PeriodicYee.fiber Concrete.material (ConventionalAnalytic.trim k) := fiber_cast _ _

/-- Explicit base-20 enumeration, with the first cell coordinate varying fastest. -/
def cellIndex : Cell20 ≃ Fin 8000 :=
  (Equiv.piCongrRight fun _ : Direction => (ZMod.finEquiv 20).symm.toEquiv).trans
    (finFunctionFinEquiv (m := 20) (n := 3))

/-- The direction is the outer index and the cell is the inner index. -/
def electricIndex : Electric20 ≃ Fin 24000 :=
  (Equiv.prodCongr (Equiv.refl Direction) cellIndex).trans finProdFinEquiv

theorem electricIndex_val (e : Electric20) :
    (electricIndex e).val = (∑ j : Direction, (e.2 j).val * 20 ^ j.val) + 8000 * e.1.val := rfl

def finiteFiber (material : Cell20 → ℚ) (k : Direction → ℤ) :
    Matrix (Fin 24000) (Fin 24000) ℚ :=
  Matrix.reindex electricIndex electricIndex (fiber material k)

theorem finiteFiber_symmetric (material : Cell20 → ℚ) (k : Direction → ℤ) :
    (finiteFiber material k).IsSymm := (fiber_symmetric material k).reindex electricIndex

theorem finiteFiber_cast (material : Cell20 → ℚ) (k : Direction → ℤ) :
    (finiteFiber material k).map ((↑) : ℚ → ℂ) =
      Matrix.reindex electricIndex electricIndex
        (PeriodicYee.fiber (fun r => (material r : ℝ)) (ConventionalAnalytic.trim k)) := by
  exact congrArg (Matrix.reindex electricIndex electricIndex) (fiber_cast material k)

noncomputable section

/-- The exact Hilbert-space coordinate change for the checker enumeration. -/
def complexCoordinates : EuclideanSpace ℂ Electric20 ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin 24000) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ electricIndex

theorem complexCoordinates_apply (x : EuclideanSpace ℂ Electric20) (i : Fin 24000) :
    complexCoordinates x i = x (electricIndex.symm i) := rfl

private theorem matrix_reindex_action {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (e : ι ≃ κ) (M : Matrix ι ι ℂ)
    (x : EuclideanSpace ℂ ι) :
    Matrix.toEuclideanCLM (n := κ) (𝕜 := ℂ) (Matrix.reindex e e M)
        (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e x) =
      LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e
        (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) M x) := by
  ext i
  change (∑ j : κ, M (e.symm i) (e.symm j) * x (e.symm j)) =
    ∑ j : ι, M (e.symm i) j * x j
  exact e.symm.sum_comp (fun j => M (e.symm i) j * x j)

/-- The rational matrix acts on exactly the reindexed conventional fiber. -/
theorem finiteFiber_intertwining (material : Cell20 → ℚ) (k : Direction → ℤ)
    (x : EuclideanSpace ℂ Electric20) :
    Maxwell.Defect.complexRationalOperator (finiteFiber material k) (complexCoordinates x) =
      complexCoordinates
        (Matrix.toEuclideanCLM (n := Electric20) (𝕜 := ℂ)
          (PeriodicYee.fiber (fun r => (material r : ℝ)) (ConventionalAnalytic.trim k)) x) := by
  rw [Maxwell.Defect.complexRationalOperator, finiteFiber_cast]
  exact matrix_reindex_action electricIndex _ x

theorem finiteFiber_conjugacy (material : Cell20 → ℚ) (k : Direction → ℤ) :
    complexCoordinates.toContinuousLinearEquiv.conjContinuousAlgEquiv
      (Matrix.toEuclideanCLM (n := Electric20) (𝕜 := ℂ)
        (PeriodicYee.fiber (fun r => (material r : ℝ)) (ConventionalAnalytic.trim k))) =
      Maxwell.Defect.complexRationalOperator (finiteFiber material k) := by
  apply ContinuousLinearMap.ext
  intro y
  obtain ⟨x, rfl⟩ := complexCoordinates.surjective y
  change complexCoordinates
    (Matrix.toEuclideanCLM (n := Electric20) (𝕜 := ℂ) _
      (complexCoordinates.symm (complexCoordinates x))) = _
  rw [complexCoordinates.symm_apply_apply]
  exact (finiteFiber_intertwining material k x).symm

/-- The real checker operator is the real restriction of that same conjugate
full fiber, not an independently specified real matrix. -/
theorem finiteFiber_realPart (material : Cell20 → ℚ) (k : Direction → ℤ) :
    Maxwell.Defect.realPartOperator
      (complexCoordinates.toContinuousLinearEquiv.conjContinuousAlgEquiv
        (Matrix.toEuclideanCLM (n := Electric20) (𝕜 := ℂ)
          (PeriodicYee.fiber (fun r => (material r : ℝ)) (ConventionalAnalytic.trim k)))) =
      Maxwell.Defect.rationalOperator (finiteFiber material k) := by
  rw [finiteFiber_conjugacy, Maxwell.Defect.realPartOperator_rational]

theorem concrete_finiteFiber_conjugacy (k : Direction → ℤ) :
    complexCoordinates.toContinuousLinearEquiv.conjContinuousAlgEquiv
      (Matrix.toEuclideanCLM (n := Electric20) (𝕜 := ℂ)
        (PeriodicYee.fiber Concrete.material (ConventionalAnalytic.trim k))) =
      Maxwell.Defect.complexRationalOperator (finiteFiber concreteMaterial k) :=
  finiteFiber_conjugacy concreteMaterial k

theorem concrete_finiteFiber_realPart (k : Direction → ℤ) :
    Maxwell.Defect.realPartOperator
      (complexCoordinates.toContinuousLinearEquiv.conjContinuousAlgEquiv
        (Matrix.toEuclideanCLM (n := Electric20) (𝕜 := ℂ)
          (PeriodicYee.fiber Concrete.material (ConventionalAnalytic.trim k)))) =
      Maxwell.Defect.rationalOperator (finiteFiber concreteMaterial k) :=
  finiteFiber_realPart concreteMaterial k

/-- Real coordinates of an actual full-cell vector in the checker ordering. -/
def finiteRealVector (φ : EuclideanSpace ℂ Electric20) : EuclideanSpace ℝ (Fin 24000) :=
  Maxwell.Defect.realCoordinatePart (complexCoordinates φ)

theorem finiteRealVector_embedding (φ : EuclideanSpace ℂ Electric20)
    (hreal : ∀ e, (φ e).im = 0) :
    Maxwell.Defect.realCoordinateEmbedding (finiteRealVector φ) = complexCoordinates φ := by
  ext i
  change (((φ (electricIndex.symm i)).re : ℝ) : ℂ) = φ (electricIndex.symm i)
  apply Complex.ext <;> simp [hreal]

theorem finiteRealVector_norm (φ : EuclideanSpace ℂ Electric20)
    (hreal : ∀ e, (φ e).im = 0) : ‖finiteRealVector φ‖ = ‖φ‖ := by
  rw [← Maxwell.Defect.realCoordinateEmbedding.norm_map, finiteRealVector_embedding φ hreal,
    complexCoordinates.norm_map]

theorem finiteRealVector_eigen (material : Cell20 → ℚ) (k : Direction → ℤ)
    (φ : EuclideanSpace ℂ Electric20) (μ : ℝ)
    (hreal : ∀ e, (φ e).im = 0)
    (heigen : Matrix.toEuclideanCLM (n := Electric20) (𝕜 := ℂ)
      (PeriodicYee.fiber (fun r => (material r : ℝ)) (ConventionalAnalytic.trim k)) φ =
        (μ : ℂ) • φ) :
    Maxwell.Defect.rationalOperator (finiteFiber material k) (finiteRealVector φ) =
      μ • finiteRealVector φ := by
  apply Maxwell.Defect.realCoordinateEmbedding.injective
  rw [Maxwell.Defect.rationalOperator_complex_intertwine, map_smul,
    finiteRealVector_embedding φ hreal, finiteFiber_intertwining material k φ, heigen, map_smul]
  rfl

/-- A real invariant eigenline cannot acquire additional real eigenvectors
when its complexification is one dimensional. -/
theorem realPartOperator_simple_of_complex {n : ℕ}
    (R : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (hreal : ∀ x : EuclideanSpace ℝ (Fin n),
      Maxwell.Defect.realCoordinateEmbedding (Maxwell.Defect.realPartOperator R x) =
        R (Maxwell.Defect.realCoordinateEmbedding x))
    (u : EuclideanSpace ℝ (Fin n)) (μ : ℝ) (hu : u ≠ 0)
    (heigen : Maxwell.Defect.realPartOperator R u = μ • u)
    (hdim : Module.finrank ℂ (Module.End.eigenspace R.toLinearMap (μ : ℂ)) = 1) :
    Module.finrank ℝ (Module.End.eigenspace (Maxwell.Defect.realPartOperator R).toLinearMap μ) = 1 := by
  have huC : Maxwell.Defect.realCoordinateEmbedding u ≠ 0 :=
    Maxwell.Defect.realCoordinateEmbedding.injective.ne (by simpa using hu)
  have huE : R (Maxwell.Defect.realCoordinateEmbedding u) =
      (μ : ℂ) • Maxwell.Defect.realCoordinateEmbedding u := by
    rw [← hreal, heigen, map_smul]
    rfl
  have hspan : Module.End.eigenspace R.toLinearMap (μ : ℂ) =
      ℂ ∙ Maxwell.Defect.realCoordinateEmbedding u :=
    eq_span_singleton_of_mem_of_finrank_eq_one hdim
      (Module.End.mem_eigenspace_iff.mpr huE) huC
  have hspace : Module.End.eigenspace (Maxwell.Defect.realPartOperator R).toLinearMap μ = ℝ ∙ u := by
    ext x
    rw [Module.End.mem_eigenspace_iff, Submodule.mem_span_singleton]
    constructor
    · intro hx
      change Maxwell.Defect.realPartOperator R x = μ • x at hx
      have hxC : R (Maxwell.Defect.realCoordinateEmbedding x) =
          (μ : ℂ) • Maxwell.Defect.realCoordinateEmbedding x := by
        rw [← hreal, hx, map_smul]
        rfl
      have hxmem : Maxwell.Defect.realCoordinateEmbedding x ∈
          ℂ ∙ Maxwell.Defect.realCoordinateEmbedding u :=
        hspan ▸ Module.End.mem_eigenspace_iff.mpr hxC
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hxmem
      refine ⟨c.re, ?_⟩
      have hr := congrArg Maxwell.Defect.realCoordinatePart hc
      ext i
      have hi := congrArg (fun v : EuclideanSpace ℝ (Fin n) => v i) hr
      simpa [Maxwell.Defect.realCoordinatePart_apply, Maxwell.Defect.realCoordinateEmbedding_apply,
        Complex.mul_re] using hi
    · rintro ⟨c, rfl⟩
      change Maxwell.Defect.realPartOperator R (c • u) = μ • c • u
      rw [map_smul, heigen, smul_comm]
  rw [hspace]
  exact finrank_span_singleton hu

private theorem isometry_intertwining_simple
    {H K : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [NormedAddCommGroup K] [NormedSpace ℂ K]
    (e : H ≃ₗᵢ[ℂ] K) (T : H →L[ℂ] H) (S : K →L[ℂ] K)
    (hinter : ∀ x, S (e x) = e (T x)) (φ : H) (μ : ℂ)
    (hφ : φ ≠ 0) (heigen : T φ = μ • φ)
    (hdim : Module.finrank ℂ (Module.End.eigenspace T.toLinearMap μ) = 1) :
    Module.finrank ℂ (Module.End.eigenspace S.toLinearMap μ) = 1 := by
  have hspan : Module.End.eigenspace T.toLinearMap μ = ℂ ∙ φ :=
    eq_span_singleton_of_mem_of_finrank_eq_one hdim (Module.End.mem_eigenspace_iff.mpr heigen) hφ
  have he : S (e φ) = μ • e φ := by rw [hinter, heigen, map_smul]
  have hspace : Module.End.eigenspace S.toLinearMap μ = ℂ ∙ e φ := by
    ext y
    rw [Module.End.mem_eigenspace_iff, Submodule.mem_span_singleton]
    constructor
    · intro hy
      have hx : T (e.symm y) = μ • e.symm y := by
        apply e.injective
        rw [← hinter, e.apply_symm_apply, map_smul, e.apply_symm_apply]
        exact hy
      have hmem : e.symm y ∈ ℂ ∙ φ := hspan ▸ Module.End.mem_eigenspace_iff.mpr hx
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
      refine ⟨c, ?_⟩
      simpa only [map_smul, e.apply_symm_apply] using congrArg e hc
    · rintro ⟨c, rfl⟩
      change S (c • e φ) = μ • c • e φ
      rw [map_smul, he, smul_comm]
  rw [hspace]
  apply finrank_span_singleton
  simpa only [map_zero] using e.injective.ne hφ

/-- The actual simple complex conventional eigenline yields the simple real
rational eigenline required by the finite source enclosure checker. -/
theorem finiteRealVector_simple (material : Cell20 → ℚ) (k : Direction → ℤ)
    (φ : EuclideanSpace ℂ Electric20) (μ : ℝ)
    (hφ : φ ≠ 0) (hreal : ∀ e, (φ e).im = 0)
    (heigen : Matrix.toEuclideanCLM (n := Electric20) (𝕜 := ℂ)
      (PeriodicYee.fiber (fun r => (material r : ℝ)) (ConventionalAnalytic.trim k)) φ =
        (μ : ℂ) • φ)
    (hdim : Module.finrank ℂ (Module.End.eigenspace
      (PeriodicYee.fiber (fun r => (material r : ℝ)) (ConventionalAnalytic.trim k)).toEuclideanLin
      (μ : ℂ)) = 1) :
    Module.finrank ℝ (Module.End.eigenspace
      (Maxwell.Defect.rationalOperator (finiteFiber material k)).toLinearMap μ) = 1 := by
  have hu : finiteRealVector φ ≠ 0 := by
    intro hz
    have hn := finiteRealVector_norm φ hreal
    rw [hz, norm_zero] at hn
    exact hφ (norm_eq_zero.mp hn.symm)
  have hc := isometry_intertwining_simple complexCoordinates
    (Matrix.toEuclideanCLM (n := Electric20) (𝕜 := ℂ)
      (PeriodicYee.fiber (fun r => (material r : ℝ)) (ConventionalAnalytic.trim k)))
    (Maxwell.Defect.complexRationalOperator (finiteFiber material k))
    (finiteFiber_intertwining material k) φ (μ : ℂ) hφ heigen hdim
  have hh := realPartOperator_simple_of_complex
    (Maxwell.Defect.complexRationalOperator (finiteFiber material k))
    (fun x => by
      rw [Maxwell.Defect.realPartOperator_rational]
      exact Maxwell.Defect.rationalOperator_complex_intertwine _ x)
    (finiteRealVector φ) μ hu
    (by
      rw [Maxwell.Defect.realPartOperator_rational]
      exact finiteRealVector_eigen material k φ μ hreal heigen) hc
  rw [Maxwell.Defect.realPartOperator_rational] at hh
  exact hh

end

end Maxwell.Spectral.ConventionalRational
