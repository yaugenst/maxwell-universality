import Maxwell.Defect.RationalResidual
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Analytic.Linear
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! The real checker acts on the actual real restriction of a complex
compression, with realness derived from convergent rational matrices. -/
namespace Maxwell.Defect

open InnerProductSpace Matrix Filter Topology Module.End

variable {n : ℕ}

/-- Coordinatewise inclusion of the real Euclidean space, preserving its
Hilbert norm exactly. -/
noncomputable def realCoordinateEmbedding :
    EuclideanSpace ℝ (Fin n) →ₗᵢ[ℝ] EuclideanSpace ℂ (Fin n) where
  toFun x := WithLp.toLp 2 (fun i => (x i : ℂ))
  map_add' x y := by ext i; simp
  map_smul' a x := by ext i; simp
  norm_map' x := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp [EuclideanSpace.norm_sq_eq]

@[simp] theorem realCoordinateEmbedding_apply (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    realCoordinateEmbedding x i = (x i : ℂ) := rfl

noncomputable def realCoordinatePart :
    EuclideanSpace ℂ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp 2 (fun i => (x i).re)
      map_add' := fun x y => by ext i; simp
      map_smul' := fun a x => by ext i; simp }

@[simp] theorem realCoordinatePart_apply (x : EuclideanSpace ℂ (Fin n)) (i : Fin n) :
    realCoordinatePart x i = (x i).re := rfl

@[simp] theorem realCoordinatePart_embedding (x : EuclideanSpace ℝ (Fin n)) :
    realCoordinatePart (realCoordinateEmbedding x) = x := by ext i; simp

theorem realCoordinatePart_norm_apply_le (x : EuclideanSpace ℂ (Fin n)) :
    ‖realCoordinatePart x‖ ≤ ‖x‖ := by
  have hs : ‖realCoordinatePart x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.norm_sq_eq]
    apply Finset.sum_le_sum
    intro i _
    have h := pow_le_pow_left₀ (abs_nonneg (x i).re) (Complex.abs_re_le_norm (x i)) 2
    simpa only [realCoordinatePart_apply, sq_abs] using h
  nlinarith [norm_nonneg (realCoordinatePart x), norm_nonneg x]

theorem realCoordinatePart_norm_le :
    ‖realCoordinatePart (n := n)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa using realCoordinatePart_norm_apply_le x

/-- The real operator extracted from a complex finite compression. -/
noncomputable def realPartOperator
    (R : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  realCoordinatePart.comp ((R.restrictScalars ℝ).comp realCoordinateEmbedding.toContinuousLinearMap)

@[simp] theorem realPartOperator_apply
    (R : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) :
    realPartOperator R x = realCoordinatePart (R (realCoordinateEmbedding x)) := rfl

noncomputable def complexRationalOperator (T : Matrix (Fin n) (Fin n) ℚ) :
    EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
  Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (T.map ((↑) : ℚ → ℂ))

/-- Rational matrix multiplication commutes exactly with the coordinate
inclusion; no realness hypothesis on a limiting operator is needed. -/
theorem rationalOperator_complex_intertwine (T : Matrix (Fin n) (Fin n) ℚ)
    (x : EuclideanSpace ℝ (Fin n)) :
    realCoordinateEmbedding (rationalOperator T x) =
      complexRationalOperator T (realCoordinateEmbedding x) := by
  ext i
  change (((∑ j, (T i j : ℝ) * x j) : ℝ) : ℂ) = ∑ j, (T i j : ℂ) * (x j : ℂ)
  simp

@[simp] theorem realPartOperator_rational (T : Matrix (Fin n) (Fin n) ℚ) :
    realPartOperator (complexRationalOperator T) = rationalOperator T := by
  apply ContinuousLinearMap.ext
  intro x
  rw [realPartOperator_apply, ← rationalOperator_complex_intertwine,
    realCoordinatePart_embedding]

theorem realPartOperator_sub
    (R S : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :
    realPartOperator (R - S) = realPartOperator R - realPartOperator S := by
  apply ContinuousLinearMap.ext
  intro x
  simp [realPartOperator]

theorem realPartOperator_norm_le
    (R : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :
    ‖realPartOperator R‖ ≤ ‖R‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  calc
    _ ≤ ‖R (realCoordinateEmbedding x)‖ := realCoordinatePart_norm_apply_le _
    _ ≤ ‖R‖ * ‖realCoordinateEmbedding x‖ := R.le_opNorm _
    _ = ‖R‖ * ‖x‖ := by rw [realCoordinateEmbedding.norm_map]

/-- The real extraction is a bounded real-linear map on operator spaces,
so it commutes with Bochner integration and preserves real analyticity. -/
noncomputable def realPartOperatorMap :
    (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) →L[ℝ]
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :=
  LinearMap.mkContinuous
    { toFun := realPartOperator
      map_add' := fun R S => by
        apply ContinuousLinearMap.ext
        intro x
        simp [realPartOperator]
      map_smul' := fun a R => by
        apply ContinuousLinearMap.ext
        intro x
        simp [realPartOperator] }
    1 (fun R => by simpa using realPartOperator_norm_le R)

@[simp] theorem realPartOperatorMap_apply
    (R : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :
    realPartOperatorMap R = realPartOperator R := rfl

theorem realPartOperatorMap_norm_le : ‖realPartOperatorMap (n := n)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro R
  simpa using realPartOperator_norm_le R

theorem realPartOperator_integral {X : Type*} [MeasurableSpace X]
    (μ : MeasureTheory.Measure X)
    (f : X → EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (hf : MeasureTheory.Integrable f μ) :
    realPartOperator (∫ x, f x ∂μ) = ∫ x, realPartOperator (f x) ∂μ := by
  exact (realPartOperatorMap.integral_comp_comm hf).symm

theorem realPartOperator_analyticAt_real
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : V → EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) (v : V)
    (hf : AnalyticAt ℝ f v) : AnalyticAt ℝ (fun x => realPartOperator (f x)) v :=
  (realPartOperatorMap.analyticAt (f v)).comp hf

/-- Extracting real coordinates cannot amplify a complex norm enclosure. -/
theorem realPartOperator_error
    (R : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (T : Matrix (Fin n) (Fin n) ℚ) :
    ‖realPartOperator R - rationalOperator T‖ ≤ ‖R - complexRationalOperator T‖ := by
  rw [← realPartOperator_rational, ← realPartOperator_sub]
  exact realPartOperator_norm_le _

theorem realCoordinatePart_inner_left (z : EuclideanSpace ℂ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) :
    inner ℝ (realCoordinatePart z) x = (inner ℂ z (realCoordinateEmbedding x)).re := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Complex.mul_re]

theorem realCoordinatePart_inner_right (x : EuclideanSpace ℝ (Fin n))
    (z : EuclideanSpace ℂ (Fin n)) :
    inner ℝ x (realCoordinatePart z) = (inner ℂ (realCoordinateEmbedding x) z).re := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Complex.mul_re]

theorem realCoordinateEmbedding_inner (x y : EuclideanSpace ℝ (Fin n)) :
    inner ℂ (realCoordinateEmbedding x) (realCoordinateEmbedding y) = (inner ℝ x y : ℂ) := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct]

/-- The complex pole's real source outer product becomes exactly the real
rank-one operator used in the finite-dimensional branch theorem. -/
theorem realPartOperator_rankOne (w : EuclideanSpace ℝ (Fin n)) :
    realPartOperator (rankOne ℂ (realCoordinateEmbedding w) (realCoordinateEmbedding w)) =
      rankOne ℝ w w := by
  apply ContinuousLinearMap.ext
  intro x
  ext i
  simp [rankOne_apply, realCoordinateEmbedding_inner]

theorem realPartOperator_symmetric
    (R : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) (hR : IsSelfAdjoint R) :
    (realPartOperator R).toLinearMap.IsSymmetric := by
  intro x y
  change inner ℝ (realCoordinatePart (R (realCoordinateEmbedding x))) y =
    inner ℝ x (realCoordinatePart (R (realCoordinateEmbedding y)))
  rw [realCoordinatePart_inner_left, realCoordinatePart_inner_right]
  exact congrArg Complex.re (hR.isSymmetric (realCoordinateEmbedding x) (realCoordinateEmbedding y))

theorem realPartOperator_tendsto
    (Rk : ℕ → EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (R : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (hlim : Tendsto Rk atTop (𝓝 R)) :
    Tendsto (fun k => realPartOperator (Rk k)) atTop (𝓝 (realPartOperator R)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) _ (tendsto_iff_norm_sub_tendsto_zero.mp hlim)
  intro k
  rw [← realPartOperator_sub]
  exact realPartOperator_norm_le _

/-- Complex norm convergence of the exact rational compression matrices
supplies real operator-norm convergence for the finite checker. -/
theorem rationalOperator_tendsto_of_complex
    (T : ℕ → Matrix (Fin n) (Fin n) ℚ)
    (R : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (hlim : Tendsto (fun k => complexRationalOperator (T k)) atTop (𝓝 R)) :
    Tendsto (fun k => rationalOperator (T k)) atTop (𝓝 (realPartOperator R)) := by
  simpa only [realPartOperator_rational] using realPartOperator_tendsto _ R hlim

/-- The limiting compression preserves the real coordinate subspace
because every approximating rational matrix does. -/
theorem realPartOperator_intertwine_of_limit
    (T : ℕ → Matrix (Fin n) (Fin n) ℚ)
    (R : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (hlim : Tendsto (fun k => complexRationalOperator (T k)) atTop (𝓝 R))
    (x : EuclideanSpace ℝ (Fin n)) :
    realCoordinateEmbedding (realPartOperator R x) = R (realCoordinateEmbedding x) := by
  have hreal := rationalOperator_tendsto_of_complex T R hlim
  have hrealApply : Tendsto (fun k => rationalOperator (T k) x) atTop
      (𝓝 (realPartOperator R x)) :=
    isBoundedBilinearMap_apply.continuous.tendsto _ |>.comp
      (hreal.prodMk_nhds (tendsto_const_nhds (x := x)))
  have hcomplexApply : Tendsto (fun k => complexRationalOperator (T k) (realCoordinateEmbedding x))
      atTop (𝓝 (R (realCoordinateEmbedding x))) :=
    isBoundedBilinearMap_apply.continuous.tendsto _ |>.comp
      (hlim.prodMk_nhds (tendsto_const_nhds (x := realCoordinateEmbedding x)))
  have hj := realCoordinateEmbedding.continuous.tendsto _ |>.comp hrealApply
  simp only [Function.comp_def, rationalOperator_complex_intertwine] at hj
  exact tendsto_nhds_unique hj hcomplexApply

/-- A certified real eigenpair is an eigenpair of the actual complex
compression; the realness needed for this conclusion is proved above. -/
theorem realPartOperator_eigenpair_lift
    (T : ℕ → Matrix (Fin n) (Fin n) ℚ)
    (R : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (hlim : Tendsto (fun k => complexRationalOperator (T k)) atTop (𝓝 R))
    (x : EuclideanSpace ℝ (Fin n)) (ν : ℝ)
    (heig : realPartOperator R x = ν • x) :
    R (realCoordinateEmbedding x) = (ν : ℂ) • realCoordinateEmbedding x := by
  rw [← realPartOperator_intertwine_of_limit T R hlim, heig, map_smul]
  ext i
  simp

@[simp] theorem realCoordinatePart_I_embedding (x : EuclideanSpace ℝ (Fin n)) :
    realCoordinatePart (Complex.I • realCoordinateEmbedding x) = 0 := by
  ext i
  simp

theorem realCoordinate_decomposition (z : EuclideanSpace ℂ (Fin n)) :
    z = realCoordinateEmbedding (realCoordinatePart z) +
      Complex.I • realCoordinateEmbedding (realCoordinatePart ((-Complex.I) • z)) := by
  ext i
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]

/-- The coordinate real-part map also intertwines whenever the complex
operator preserves the real coordinate subspace. -/
theorem realPartOperator_commute_part
    (R : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (hreal : ∀ x : EuclideanSpace ℝ (Fin n),
      realCoordinateEmbedding (realPartOperator R x) = R (realCoordinateEmbedding x))
    (z : EuclideanSpace ℂ (Fin n)) :
    realCoordinatePart (R z) = realPartOperator R (realCoordinatePart z) := by
  have hsplit : R z = realCoordinateEmbedding (realPartOperator R (realCoordinatePart z)) +
      Complex.I • realCoordinateEmbedding
        (realPartOperator R (realCoordinatePart ((-Complex.I) • z))) := by
    calc
      R z = R (realCoordinateEmbedding (realCoordinatePart z) +
          Complex.I • realCoordinateEmbedding (realCoordinatePart ((-Complex.I) • z))) :=
        congrArg R (realCoordinate_decomposition z)
      _ = _ := by rw [map_add, map_smul, ← hreal, ← hreal]
  rw [hsplit, map_add, realCoordinatePart_embedding, realCoordinatePart_I_embedding, add_zero]

theorem realPartOperator_eigenvector_part
    (R : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (hreal : ∀ x : EuclideanSpace ℝ (Fin n),
      realCoordinateEmbedding (realPartOperator R x) = R (realCoordinateEmbedding x))
    (z : EuclideanSpace ℂ (Fin n)) (ν : ℝ) (hz : R z = (ν : ℂ) • z) :
    realPartOperator R (realCoordinatePart z) = ν • realCoordinatePart z := by
  rw [← realPartOperator_commute_part R hreal, hz]
  ext i
  simp

/-- Complexifying the selected real eigenline creates no extra
eigenvectors: real and imaginary parts lie on that same real line. -/
theorem realPartOperator_complex_eigenspace
    (R : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (hreal : ∀ x : EuclideanSpace ℝ (Fin n),
      realCoordinateEmbedding (realPartOperator R x) = R (realCoordinateEmbedding x))
    (x : EuclideanSpace ℝ (Fin n)) (ν : ℝ) (hx : x ≠ 0)
    (heig : realPartOperator R x = ν • x)
    (hsimple : Module.finrank ℝ (eigenspace (realPartOperator R).toLinearMap ν) = 1) :
    eigenspace R.toLinearMap (ν : ℂ) = ℂ ∙ realCoordinateEmbedding x := by
  have hspan : eigenspace (realPartOperator R).toLinearMap ν = ℝ ∙ x :=
    eq_span_singleton_of_mem_of_finrank_eq_one hsimple (mem_eigenspace_iff.mpr heig) hx
  have hselected : R (realCoordinateEmbedding x) = (ν : ℂ) • realCoordinateEmbedding x := by
    rw [← hreal, heig, map_smul]
    ext i
    simp
  ext z
  rw [mem_eigenspace_iff, Submodule.mem_span_singleton]
  constructor
  · intro hz
    change R z = (ν : ℂ) • z at hz
    have hre := realPartOperator_eigenvector_part R hreal z ν hz
    have hI : R ((-Complex.I) • z) = (ν : ℂ) • ((-Complex.I) • z) := by
      rw [map_smul, hz, smul_comm]
    have him := realPartOperator_eigenvector_part R hreal ((-Complex.I) • z) ν hI
    have hreMem : realCoordinatePart z ∈ ℝ ∙ x := hspan ▸ mem_eigenspace_iff.mpr hre
    have himMem : realCoordinatePart ((-Complex.I) • z) ∈ ℝ ∙ x :=
      hspan ▸ mem_eigenspace_iff.mpr him
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hreMem
    obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp himMem
    refine ⟨(a : ℂ) + Complex.I * (b : ℂ), ?_⟩
    calc
      _ = realCoordinateEmbedding (a • x) + Complex.I • realCoordinateEmbedding (b • x) := by
        ext i
        simp only [PiLp.smul_apply, PiLp.add_apply, realCoordinateEmbedding_apply, smul_eq_mul,
          Complex.ofReal_mul]
        ring
      _ = z := by rw [ha, hb]; exact (realCoordinate_decomposition z).symm
  · rintro ⟨c, rfl⟩
    change R (c • realCoordinateEmbedding x) = (ν : ℂ) • (c • realCoordinateEmbedding x)
    rw [map_smul, hselected, smul_comm]

/-- A simple real eigenpair remains simple over the complex scalars of
the actual compressed resolvent. -/
theorem realPartOperator_simple_complex
    (R : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (hreal : ∀ x : EuclideanSpace ℝ (Fin n),
      realCoordinateEmbedding (realPartOperator R x) = R (realCoordinateEmbedding x))
    (x : EuclideanSpace ℝ (Fin n)) (ν : ℝ) (hx : x ≠ 0)
    (heig : realPartOperator R x = ν • x)
    (hsimple : Module.finrank ℝ (eigenspace (realPartOperator R).toLinearMap ν) = 1) :
    Module.finrank ℂ (eigenspace R.toLinearMap (ν : ℂ)) = 1 := by
  rw [realPartOperator_complex_eigenspace R hreal x ν hx heig hsimple]
  apply finrank_span_singleton
  exact realCoordinateEmbedding.injective.ne (by simpa using hx)

theorem realPartOperator_simple_complex_of_limit
    (T : ℕ → Matrix (Fin n) (Fin n) ℚ)
    (R : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (hlim : Tendsto (fun k => complexRationalOperator (T k)) atTop (𝓝 R))
    (x : EuclideanSpace ℝ (Fin n)) (ν : ℝ) (hx : x ≠ 0)
    (heig : realPartOperator R x = ν • x)
    (hsimple : Module.finrank ℝ (eigenspace (realPartOperator R).toLinearMap ν) = 1) :
    Module.finrank ℂ (eigenspace R.toLinearMap (ν : ℂ)) = 1 :=
  realPartOperator_simple_complex R (realPartOperator_intertwine_of_limit T R hlim)
    x ν hx heig hsimple

end Maxwell.Defect
