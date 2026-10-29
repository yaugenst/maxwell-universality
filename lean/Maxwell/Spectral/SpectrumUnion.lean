import Mathlib.Analysis.CStarAlgebra.ContinuousMap
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Topology.ContinuousMap.Units
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Spectrum of continuous finite matrix multiplication on L²

The representation is constructed by multiplication of actual functions,
using Hölder's inequality to descend to L² equivalence classes.
-/

namespace Maxwell.Spectral

open MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator

noncomputable section

theorem continuousMap_spectrum_union {X R 𝕜 : Type*} [TopologicalSpace X]
    [NormedRing R] [CompleteSpace R] [CommRing 𝕜] [Algebra 𝕜 R]
    (f : C(X, R)) : spectrum 𝕜 f = ⋃ x, spectrum 𝕜 (f x) := by
  ext z
  simp only [spectrum.mem_iff, ContinuousMap.isUnit_iff_forall_isUnit,
    not_forall, Set.mem_iUnion, ContinuousMap.sub_apply,
    Algebra.algebraMap_eq_smul_one, ContinuousMap.smul_apply, ContinuousMap.one_apply]

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
variable [MeasurableSpace X] [BorelSpace X]
variable (μ : Measure X) [IsFiniteMeasure μ]

abbrev ScalarL2 := Lp ℂ 2 μ

def scalarMultiplier (f : C(X, ℂ)) : ScalarL2 μ →L[ℂ] ScalarL2 μ :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL μ ∞ 2 2 (ContinuousMap.toLp ∞ μ ℂ f)

theorem scalarMultiplier_ae (f : C(X, ℂ)) (u : ScalarL2 μ) :
    scalarMultiplier μ f u =ᵐ[μ] fun t => f t * u t := by
  have h := (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder
    (ContinuousMap.toLp ∞ μ ℂ f) u (r := 2)
  filter_upwards [h, ContinuousMap.coeFn_toLp μ (p := ∞) (𝕜 := ℂ) f] with t ht hf
  change ((ContinuousLinearMap.mul ℂ ℂ).holder 2 (ContinuousMap.toLp ∞ μ ℂ f) u) t = _
  simpa only [hf, ContinuousLinearMap.mul_apply'] using ht

theorem scalarMultiplier_add (f g : C(X, ℂ)) :
    scalarMultiplier μ (f + g) = scalarMultiplier μ f + scalarMultiplier μ g := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [scalarMultiplier_ae μ (f + g) u,
    scalarMultiplier_ae μ f u, scalarMultiplier_ae μ g u,
    Lp.coeFn_add (scalarMultiplier μ f u) (scalarMultiplier μ g u)] with t hfg hf hg hadd
  change (scalarMultiplier μ (f + g) u) t = ((scalarMultiplier μ f u) + (scalarMultiplier μ g u)) t
  rw [hfg, hadd, Pi.add_apply, hf, hg, ContinuousMap.add_apply, add_mul]

theorem scalarMultiplier_mul (f g : C(X, ℂ)) :
    scalarMultiplier μ (f * g) = (scalarMultiplier μ f).comp (scalarMultiplier μ g) := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [scalarMultiplier_ae μ (f * g) u,
    scalarMultiplier_ae μ f (scalarMultiplier μ g u), scalarMultiplier_ae μ g u]
    with t hfg hf hg
  change (scalarMultiplier μ (f * g) u) t = (scalarMultiplier μ f (scalarMultiplier μ g u)) t
  rw [hfg, hf, hg, ContinuousMap.mul_apply, mul_assoc]

theorem scalarMultiplier_const (c : ℂ) :
    scalarMultiplier μ (ContinuousMap.const X c) = c • ContinuousLinearMap.id ℂ (ScalarL2 μ) := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [scalarMultiplier_ae μ (ContinuousMap.const X c) u, Lp.coeFn_smul c u]
    with t hf hc
  change (scalarMultiplier μ (ContinuousMap.const X c) u) t = (c • u) t
  simpa only [ContinuousMap.const_apply, hc, Pi.smul_apply, smul_eq_mul] using hf

theorem scalarMultiplier_star (f : C(X, ℂ)) :
    scalarMultiplier μ (star f) = (scalarMultiplier μ f).adjoint := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro u v
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [scalarMultiplier_ae μ (star f) u, scalarMultiplier_ae μ f v]
    with t hu hv
  rw [hu, hv]
  simp [ContinuousMap.star_apply, RCLike.inner_apply, mul_comm, mul_assoc]

def scalarMultiplierHom : C(X, ℂ) →⋆ₐ[ℂ] (ScalarL2 μ →L[ℂ] ScalarL2 μ) where
  toFun := scalarMultiplier μ
  map_one' := by
    change scalarMultiplier μ (ContinuousMap.const X 1) = ContinuousLinearMap.id ℂ _
    rw [scalarMultiplier_const, one_smul]
  map_mul' := scalarMultiplier_mul μ
  map_zero' := by
    change scalarMultiplier μ (ContinuousMap.const X 0) = 0
    rw [scalarMultiplier_const]
    apply ContinuousLinearMap.ext
    intro u
    change (0 : ℂ) • u = 0
    exact zero_smul ℂ u
  map_add' := scalarMultiplier_add μ
  commutes' c := by
    change scalarMultiplier μ (ContinuousMap.const X c) = c • ContinuousLinearMap.id ℂ _
    exact scalarMultiplier_const μ c
  map_star' := scalarMultiplier_star μ

theorem scalarMultiplier_on_one (f : C(X, ℂ)) :
    scalarMultiplier μ f (ContinuousMap.toLp 2 μ ℂ (1 : C(X, ℂ))) =
      ContinuousMap.toLp 2 μ ℂ f := by
  apply Lp.ext
  filter_upwards [scalarMultiplier_ae μ f (ContinuousMap.toLp 2 μ ℂ (1 : C(X, ℂ))),
    ContinuousMap.coeFn_toLp μ (p := 2) (𝕜 := ℂ) (1 : C(X, ℂ)),
    ContinuousMap.coeFn_toLp μ (p := 2) (𝕜 := ℂ) f]
    with t hm h1 hf
  simpa only [h1, ContinuousMap.one_apply, mul_one, hf] using hm

theorem scalarMultiplier_injective [μ.IsOpenPosMeasure] :
    Function.Injective (scalarMultiplier μ) := by
  intro f g h
  apply ContinuousMap.toLp_injective μ (p := 2) (𝕜 := ℂ)
  rw [← scalarMultiplier_on_one μ f, ← scalarMultiplier_on_one μ g, h]

variable {n : Type*} [Fintype n] [DecidableEq n]

abbrev MatrixL2 := PiLp 2 (fun _ : n => ScalarL2 μ)

def continuousEntry (f : C(X, Matrix n n ℂ)) (i j : n) : C(X, ℂ) :=
  ⟨fun t => f t i j,
    (continuous_apply j).comp ((continuous_apply i).comp f.continuous)⟩

def matrixMultiplier (f : C(X, Matrix n n ℂ)) :
    MatrixL2 (n := n) μ →L[ℂ] MatrixL2 (n := n) μ :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : n => ScalarL2 μ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i => ∑ j,
      (scalarMultiplier μ (continuousEntry f i j)).comp
        (PiLp.proj 2 (fun _ : n => ScalarL2 μ) j))

omit [DecidableEq n] in
theorem matrixMultiplier_apply (f : C(X, Matrix n n ℂ)) (u : MatrixL2 (n := n) μ) (i : n) :
    matrixMultiplier μ f u i = ∑ j, scalarMultiplier μ (continuousEntry f i j) (u j) := by
  simp [matrixMultiplier]

omit [DecidableEq n] in
theorem matrixMultiplier_ae (f : C(X, Matrix n n ℂ)) (u : MatrixL2 (n := n) μ) (i : n) :
    matrixMultiplier μ f u i =ᵐ[μ] fun t => (f t).mulVec (fun j => u j t) i := by
  rw [matrixMultiplier_apply]
  filter_upwards [Lp.coeFn_finsetSum Finset.univ
    (fun j => scalarMultiplier μ (continuousEntry f i j) (u j)),
    Filter.eventually_all.mpr (fun j => scalarMultiplier_ae μ (continuousEntry f i j) (u j))]
    with t hsum hterm
  simp only [Finset.sum_apply] at hsum
  rw [hsum]
  apply Finset.sum_congr rfl
  intro j _
  exact hterm j

omit [DecidableEq n] in
theorem matrixMultiplier_add (f g : C(X, Matrix n n ℂ)) :
    matrixMultiplier μ (f + g) = matrixMultiplier μ f + matrixMultiplier μ g := by
  apply ContinuousLinearMap.ext
  intro u
  apply PiLp.ext
  intro i
  apply Lp.ext
  filter_upwards [matrixMultiplier_ae μ (f + g) u i,
    matrixMultiplier_ae μ f u i, matrixMultiplier_ae μ g u i,
    Lp.coeFn_add (matrixMultiplier μ f u i) (matrixMultiplier μ g u i)] with t hfg hf hg ha
  change (matrixMultiplier μ (f + g) u i) t =
    (matrixMultiplier μ f u i + matrixMultiplier μ g u i) t
  rw [hfg, ha, Pi.add_apply, hf, hg]
  exact congrFun (Matrix.add_mulVec (f t) (g t) (fun j => u j t)) i

omit [DecidableEq n] in
theorem matrixMultiplier_mul (f g : C(X, Matrix n n ℂ)) :
    matrixMultiplier μ (f * g) = (matrixMultiplier μ f).comp (matrixMultiplier μ g) := by
  apply ContinuousLinearMap.ext
  intro u
  apply PiLp.ext
  intro i
  apply Lp.ext
  filter_upwards [matrixMultiplier_ae μ (f * g) u i,
    matrixMultiplier_ae μ f (matrixMultiplier μ g u) i,
    Filter.eventually_all.mpr (fun j => matrixMultiplier_ae μ g u j)] with t hfg hf hg
  change (matrixMultiplier μ (f * g) u i) t = (matrixMultiplier μ f (matrixMultiplier μ g u) i) t
  rw [hfg, hf]
  simp only [hg, ContinuousMap.mul_apply]
  exact congrFun (Matrix.mulVec_mulVec (fun j => u j t) (f t) (g t)).symm i

theorem matrixMultiplier_const_scalar (c : ℂ) :
    matrixMultiplier μ (ContinuousMap.const X (c • (1 : Matrix n n ℂ))) =
      c • ContinuousLinearMap.id ℂ (MatrixL2 (n := n) μ) := by
  apply ContinuousLinearMap.ext
  intro u
  apply PiLp.ext
  intro i
  apply Lp.ext
  filter_upwards [matrixMultiplier_ae μ (ContinuousMap.const X (c • (1 : Matrix n n ℂ))) u i,
    Lp.coeFn_smul c (u i)] with t hm hc
  change (matrixMultiplier μ (ContinuousMap.const X (c • (1 : Matrix n n ℂ))) u i) t =
    (c • u i) t
  rw [hm, hc]
  simp [Matrix.smul_mulVec]

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] [Fintype n] [DecidableEq n] in
theorem continuousEntry_star (f : C(X, Matrix n n ℂ)) (i j : n) :
    continuousEntry (star f) i j = star (continuousEntry f j i) := by
  ext t
  rfl

omit [DecidableEq n] in
theorem matrixMultiplier_star (f : C(X, Matrix n n ℂ)) :
    matrixMultiplier μ (star f) = (matrixMultiplier μ f).adjoint := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro u v
  simp only [PiLp.inner_apply, matrixMultiplier_apply, sum_inner, inner_sum,
    continuousEntry_star, scalarMultiplier_star, ContinuousLinearMap.adjoint_inner_left]
  exact Finset.sum_comm

def matrixMultiplierHom : C(X, Matrix n n ℂ) →⋆ₐ[ℂ]
    (MatrixL2 (n := n) μ →L[ℂ] MatrixL2 (n := n) μ) where
  toFun := matrixMultiplier μ
  map_one' := by
    change matrixMultiplier μ (ContinuousMap.const X 1) = ContinuousLinearMap.id ℂ _
    have h := matrixMultiplier_const_scalar (n := n) μ (1 : ℂ)
    simpa only [one_smul] using h
  map_mul' := matrixMultiplier_mul μ
  map_zero' := by
    change matrixMultiplier μ (ContinuousMap.const X 0) = 0
    have h := matrixMultiplier_const_scalar (n := n) μ (0 : ℂ)
    simp only [zero_smul] at h
    rw [h]
    apply ContinuousLinearMap.ext
    intro u
    exact zero_smul ℂ u
  map_add' := matrixMultiplier_add μ
  commutes' c := by
    simp only [Algebra.algebraMap_eq_smul_one]
    change matrixMultiplier μ (ContinuousMap.const X (c • (1 : Matrix n n ℂ))) =
      c • ContinuousLinearMap.id ℂ _
    exact matrixMultiplier_const_scalar μ c
  map_star' := matrixMultiplier_star μ

theorem matrixMultiplier_single (f : C(X, Matrix n n ℂ)) (u : ScalarL2 μ) (i j : n) :
    matrixMultiplier μ f (PiLp.single 2 j u) i =
      scalarMultiplier μ (continuousEntry f i j) u := by
  simp [matrixMultiplier_apply, PiLp.single_apply, apply_ite]

theorem matrixMultiplier_injective [μ.IsOpenPosMeasure] :
    Function.Injective (matrixMultiplier (n := n) μ) := by
  intro f g h
  apply ContinuousMap.ext
  intro t
  apply Matrix.ext
  intro i j
  have hentry : continuousEntry f i j = continuousEntry g i j := by
    apply ContinuousMap.toLp_injective μ (p := 2) (𝕜 := ℂ)
    have heval := congrArg (fun T : MatrixL2 (n := n) μ →L[ℂ] MatrixL2 (n := n) μ =>
      T (PiLp.single 2 j (ContinuousMap.toLp 2 μ ℂ (1 : C(X, ℂ)))) i) h
    simpa only [matrixMultiplier_single, scalarMultiplier_on_one] using heval
  exact congrArg (fun a : C(X, ℂ) => a t) hentry

theorem matrixMultiplier_spectrum_real [μ.IsOpenPosMeasure]
    (f : C(X, Matrix n n ℂ)) (hf : ∀ t, (f t).IsHermitian) :
    spectrum ℝ (matrixMultiplier μ f) = ⋃ t, spectrum ℝ (f t) := by
  let _ : ContinuousFunctionalCalculus ℝ C(X, Matrix n n ℂ) IsSelfAdjoint :=
    (IsSelfAdjoint.instIsometricContinuousFunctionalCalculus
      (A := C(X, Matrix n n ℂ))).toContinuousFunctionalCalculus
  let _ : ContinuousFunctionalCalculus ℝ
      (MatrixL2 (n := n) μ →L[ℂ] MatrixL2 (n := n) μ) IsSelfAdjoint :=
    (IsSelfAdjoint.instIsometricContinuousFunctionalCalculus
      (A := MatrixL2 (n := n) μ →L[ℂ] MatrixL2 (n := n) μ)).toContinuousFunctionalCalculus
  have hsa : IsSelfAdjoint f := by
    apply ContinuousMap.ext
    intro t
    exact (hf t).eq
  have hi : Function.Injective (matrixMultiplierHom (n := n) μ) :=
    matrixMultiplier_injective μ
  calc
    spectrum ℝ (matrixMultiplier μ f) = spectrum ℝ f := hsa.map_spectrum_real
      (matrixMultiplierHom μ) hi (NonUnitalStarAlgHom.isometry (matrixMultiplierHom μ) hi).continuous
    _ = _ := continuousMap_spectrum_union f

set_option maxHeartbeats 600000 in
/-- The same equality in the complex resolvent algebra. Selfadjointness
rules out nonreal spectral points on both sides. -/
theorem matrixMultiplier_spectrum_complex [μ.IsOpenPosMeasure]
    (f : C(X, Matrix n n ℂ)) (hf : ∀ t, (f t).IsHermitian) :
    spectrum ℂ (matrixMultiplier μ f) = ⋃ t, spectrum ℂ (f t) := by
  have hsa : IsSelfAdjoint f := by
    apply ContinuousMap.ext
    intro t
    exact (hf t).eq
  have hm : IsSelfAdjoint (matrixMultiplier μ f) := hsa.map (matrixMultiplierHom μ)
  have hreal := matrixMultiplier_spectrum_real μ f hf
  ext z
  constructor
  · intro hz
    have heq := hm.mem_spectrum_eq_re hz
    have hr : z.re ∈ spectrum ℝ (matrixMultiplier μ f) :=
      (spectrum.algebraMap_mem_iff ℂ (R := ℝ) (a := matrixMultiplier μ f)).mp (heq ▸ hz)
    rw [hreal] at hr
    obtain ⟨t, ht⟩ := Set.mem_iUnion.mp hr
    apply Set.mem_iUnion.mpr
    refine ⟨t, ?_⟩
    have hc : (z.re : ℂ) ∈ spectrum ℂ (f t) :=
      (spectrum.algebraMap_mem_iff ℂ (R := ℝ) (a := f t)).mpr ht
    simpa only [← heq] using hc
  · intro hz
    obtain ⟨t, ht⟩ := Set.mem_iUnion.mp hz
    have hs : IsSelfAdjoint (f t) := (hf t).eq
    have heq := hs.mem_spectrum_eq_re ht
    have hr : z.re ∈ spectrum ℝ (f t) :=
      (spectrum.algebraMap_mem_iff ℂ (R := ℝ) (a := f t)).mp (heq ▸ ht)
    have hmr : z.re ∈ spectrum ℝ (matrixMultiplier μ f) := by
      rw [hreal]
      exact Set.mem_iUnion.mpr ⟨t, hr⟩
    have hc : (z.re : ℂ) ∈ spectrum ℂ (matrixMultiplier μ f) :=
      (spectrum.algebraMap_mem_iff ℂ (R := ℝ) (a := matrixMultiplier μ f)).mpr hmr
    simpa only [← heq] using hc

end
end Maxwell.Spectral
