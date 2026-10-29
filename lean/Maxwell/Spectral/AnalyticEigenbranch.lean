import Maxwell.Green.Implicit
import Maxwell.Spectral.SimpleSplitting
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! Analytic eigenbranches constructed from a simple complementary block.

The hypothesis at the center is an explicit direct-sum decomposition with
an invertible complementary block. No eigenbranch or analytic projector is
assumed. The normalized eigenpair is obtained from the analytic implicit
function theorem, whose normal derivative is explicitly inverted.
-/

noncomputable section

namespace Maxwell.Spectral.AnalyticEigenbranch

open Filter
open scoped Topology

variable {W E : Type*}
variable [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]
variable [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- The analytic implicit-function argument also applies to vector-valued
normal variables. This constructs the function from the inverse theorem. -/
theorem analyticAt_vector_implicitFunction
    {D : W × E → E} {D' : W × E →L[ℂ] E} {z₀ : W × E}
    (hD : AnalyticAt ℂ D z₀) (hd : HasStrictFDerivAt D D' z₀)
    (hi : (D' ∘L ContinuousLinearMap.inr ℂ W E).IsInvertible) :
    AnalyticAt ℂ (hd.implicitFunctionOfProdDomain hi) z₀.1 := by
  let φ := hd.implicitFunctionDataOfProdDomain hi
  have ha : AnalyticAt ℂ φ.toOpenPartialHomeomorph φ.pt := hD.prod analyticAt_fst
  have hs := φ.toOpenPartialHomeomorph.analyticAt_symm'
    φ.pt_mem_toOpenPartialHomeomorph_source ha φ.hasStrictFDerivAt.hasFDerivAt.fderiv
  have hpair : AnalyticAt ℂ (fun x : W => (D z₀, x)) z₀.1 :=
    analyticAt_const.prod analyticAt_id
  exact analyticAt_snd.comp (hs.comp_of_eq hpair rfl)

theorem exists_analytic_vector_implicit_root
    (D : W × E → E) (hD : AnalyticAt ℂ D (0, 0)) (hzero : D (0, 0) = 0)
    (hi : (fderiv ℂ D (0, 0) ∘L ContinuousLinearMap.inr ℂ W E).IsInvertible) :
    ∃ p : W → E,
      p 0 = 0 ∧ AnalyticAt ℂ p 0 ∧
      (∀ᶠ w in 𝓝 (0 : W), D (w, p w) = 0) ∧
      (∀ᶠ z in 𝓝 ((0, 0) : W × E), D z = 0 ↔ p z.1 = z.2) := by
  have hd : HasStrictFDerivAt D (fderiv ℂ D (0, 0)) (0, 0) := hD.hasStrictFDerivAt
  let p := hd.implicitFunctionOfProdDomain hi
  have hp₀ : p 0 = 0 :=
    (hd.eventually_apply_eq_iff_implicitFunctionOfProdDomain hi).self_of_nhds.mp rfl
  refine ⟨p, hp₀, analyticAt_vector_implicitFunction hD hd hi, ?_, ?_⟩
  · simpa only [hzero] using hd.eventually_apply_implicitFunctionOfProdDomain hi
  · simpa only [hzero] using hd.eventually_apply_eq_iff_implicitFunctionOfProdDomain hi

omit [CompleteSpace W] [CompleteSpace E] in
/-- Evaluation of an analytic operator family on an analytic vector. -/
theorem analyticAt_apply {A : W → E →L[ℂ] E} {u : W → E} {w : W}
    (hA : AnalyticAt ℂ A w) (hu : AnalyticAt ℂ u w) :
    AnalyticAt ℂ (fun z => A z (u z)) w :=
  ((ContinuousLinearMap.id ℂ (E →L[ℂ] E)).analyticAt_bilinear _).comp₂ hA hu

/-- Residual for eigenvalue `energy + a` and eigenvector normalized to `(1,v)`.
Both the scalar eigenvalue increment and complementary vector are unknown. -/
def normalizedResidual
    (A : W → (ℂ × E) →L[ℂ] (ℂ × E)) (energy : ℂ)
    (z : W × (ℂ × E)) : ℂ × E :=
  A z.1 (1, z.2.2) - (energy + z.2.1) • (1, z.2.2)

omit [CompleteSpace W] [CompleteSpace E] in
theorem normalizedResidual_analytic
    (A : W → (ℂ × E) →L[ℂ] (ℂ × E)) (energy : ℂ)
    (hA : AnalyticAt ℂ A 0) :
    AnalyticAt ℂ (normalizedResidual A energy) (0, 0) := by
  have hv : AnalyticAt ℂ (fun z : W × (ℂ × E) => ((1 : ℂ), z.2.2)) (0, 0) :=
    analyticAt_const.prod (analyticAt_snd.comp analyticAt_snd)
  have ha : AnalyticAt ℂ (fun z : W × (ℂ × E) => A z.1) (0, 0) :=
    hA.comp_of_eq analyticAt_fst rfl
  have he : AnalyticAt ℂ (fun z : W × (ℂ × E) => energy + z.2.1) (0, 0) :=
    analyticAt_const.add (analyticAt_fst.comp analyticAt_snd)
  exact (analyticAt_apply ha hv).sub (he.smul hv)

/-- Explicit inverse of the normal derivative. The eigenvalue direction
is negated and the complementary direction uses the supplied inverse. -/
def normalEquiv (B : E ≃L[ℂ] E) : (ℂ × E) ≃L[ℂ] (ℂ × E) :=
  (ContinuousLinearEquiv.neg ℂ : ℂ ≃L[ℂ] ℂ).prodCongr B

omit [CompleteSpace E] in
@[simp] theorem normalEquiv_apply (B : E ≃L[ℂ] E) (z : ℂ × E) :
    normalEquiv B z = (-z.1, B z.2) := rfl

omit [CompleteSpace W] [CompleteSpace E] [NormedSpace ℂ W] in
theorem normalizedResidual_center
    (A : W → (ℂ × E) →L[ℂ] (ℂ × E)) (energy : ℂ) (B : E ≃L[ℂ] E)
    (hcenter : ∀ z : ℂ × E, A 0 z = (energy * z.1, energy • z.2 + B z.2))
    (z : ℂ × E) :
    normalizedResidual A energy (0, z) = (-z.1, B z.2 - z.1 • z.2) := by
  apply Prod.ext
  · simp [normalizedResidual, hcenter, smul_eq_mul]
  · simp [normalizedResidual, hcenter, add_smul]

omit [CompleteSpace W] [CompleteSpace E] [NormedSpace ℂ W] in
theorem normalizedResidual_normal_derivative
    (A : W → (ℂ × E) →L[ℂ] (ℂ × E)) (energy : ℂ) (B : E ≃L[ℂ] E)
    (hcenter : ∀ z : ℂ × E, A 0 z = (energy * z.1, energy • z.2 + B z.2)) :
    HasFDerivAt (fun z => normalizedResidual A energy (0, z))
      (normalEquiv B : (ℂ × E) →L[ℂ] (ℂ × E)) 0 := by
  have hfst : HasFDerivAt (fun z : ℂ × E => -z.1)
      (-ContinuousLinearMap.fst ℂ ℂ E) 0 := hasFDerivAt_fst.neg
  have hB : HasFDerivAt (fun z : ℂ × E => B z.2)
      ((B : E →L[ℂ] E).comp (ContinuousLinearMap.snd ℂ ℂ E)) 0 :=
    B.hasFDerivAt.comp 0 hasFDerivAt_snd
  have hmul : HasFDerivAt (fun z : ℂ × E => z.1 • z.2)
      (0 : (ℂ × E) →L[ℂ] E) 0 := by
    convert (hasFDerivAt_fst (𝕜 := ℂ) (p := (0 : ℂ × E))).smul
      (hasFDerivAt_snd (𝕜 := ℂ) (p := (0 : ℂ × E))) using 1
    simp
  convert hfst.prodMk (hB.sub hmul) using 1
  · funext z
    exact normalizedResidual_center A energy B hcenter z
  · ext z <;> simp [normalEquiv]

omit [CompleteSpace W] [CompleteSpace E] in
theorem normalizedResidual_normal_invertible
    (A : W → (ℂ × E) →L[ℂ] (ℂ × E)) (energy : ℂ) (B : E ≃L[ℂ] E)
    (hA : AnalyticAt ℂ A 0)
    (hcenter : ∀ z : ℂ × E, A 0 z = (energy * z.1, energy • z.2 + B z.2)) :
    (fderiv ℂ (normalizedResidual A energy) (0, 0) ∘L
      ContinuousLinearMap.inr ℂ W (ℂ × E)).IsInvertible := by
  have hd := (normalizedResidual_analytic A energy hA).differentiableAt.hasFDerivAt
  have hc := hd.comp 0 (ContinuousLinearMap.inr ℂ W (ℂ × E)).hasFDerivAt
  have heq := hc.unique (normalizedResidual_normal_derivative A energy B hcenter)
  rw [heq]
  exact ContinuousLinearMap.isInvertible_equiv

/-- An analytic eigenvalue and a nowhere-zero, first-coordinate-normalized
analytic eigenvector are constructed near a simple center eigenvalue.
The final clause is joint local uniqueness, not just uniqueness among
preselected analytic branches. The complement inverse is used only at the
center, and its normal-derivative invertibility was proved above. -/
theorem exists_analytic_normalized_eigenpair
    (A : W → (ℂ × E) →L[ℂ] (ℂ × E)) (energy : ℂ) (B : E ≃L[ℂ] E)
    (hA : AnalyticAt ℂ A 0)
    (hcenter : ∀ z : ℂ × E, A 0 z = (energy * z.1, energy • z.2 + B z.2)) :
    ∃ value : W → ℂ, ∃ vector : W → ℂ × E,
      value 0 = energy ∧ vector 0 = (1, 0) ∧
      AnalyticAt ℂ value 0 ∧ AnalyticAt ℂ vector 0 ∧
      (∀ w, (vector w).1 = 1 ∧ vector w ≠ 0) ∧
      (∀ᶠ w in 𝓝 (0 : W), A w (vector w) = value w • vector w) ∧
      (∀ᶠ z in 𝓝 ((0, 0) : W × (ℂ × E)),
        A z.1 (1, z.2.2) = (energy + z.2.1) • (1, z.2.2) ↔
          value z.1 = energy + z.2.1 ∧ (vector z.1).2 = z.2.2) := by
  have hz : normalizedResidual A energy (0, 0) = 0 := by
    rw [normalizedResidual_center A energy B hcenter]
    simp
  obtain ⟨p, hp₀, hp, hsolve, hunique⟩ := exists_analytic_vector_implicit_root
    (normalizedResidual A energy) (normalizedResidual_analytic A energy hA) hz
    (normalizedResidual_normal_invertible A energy B hA hcenter)
  refine ⟨fun w => energy + (p w).1, fun w => (1, (p w).2), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hp₀]
  · simp [hp₀]
  · exact analyticAt_const.add (analyticAt_fst.comp hp)
  · exact analyticAt_const.prod (analyticAt_snd.comp hp)
  · intro w
    refine ⟨rfl, ?_⟩
    intro h
    have hh := congrArg Prod.fst h
    simp at hh
  · filter_upwards [hsolve] with w hw
    exact sub_eq_zero.mp hw
  · filter_upwards [hunique] with z hz
    simpa only [normalizedResidual, sub_eq_zero, Prod.mk.injEq, Prod.ext_iff,
      add_right_inj] using hz

omit [CompleteSpace W] [CompleteSpace E] [NormedSpace ℂ W] in
/-- Inversion covariance of the actual operator family and the constructed
joint uniqueness imply an even eigenvalue branch. The vector transforms by
the fixed complementary inversion; symmetry of an unknown branch is not
assumed. This lemma applies to the witnesses constructed above. -/
theorem eigenpair_inversion_of_local_uniqueness
    (A : W → (ℂ × E) →L[ℂ] (ℂ × E)) (energy : ℂ)
    (value : W → ℂ) (vector : W → ℂ × E) (J : E ≃L[ℂ] E)
    (hv0 : value 0 = energy) (hu0 : vector 0 = (1, 0))
    (hv : ContinuousAt value 0) (hu : ContinuousAt vector 0)
    (hnorm : ∀ w, (vector w).1 = 1)
    (hsolve : ∀ᶠ w in 𝓝 (0 : W), A w (vector w) = value w • vector w)
    (hunique : ∀ᶠ z in 𝓝 ((0, 0) : W × (ℂ × E)),
      A z.1 (1, z.2.2) = (energy + z.2.1) • (1, z.2.2) ↔
        value z.1 = energy + z.2.1 ∧ (vector z.1).2 = z.2.2)
    (hsym : ∀ (w : W) (z : ℂ × E),
      A (-w) (z.1, J z.2) = ((A w z).1, J (A w z).2)) :
    ∀ᶠ w in 𝓝 (0 : W),
      value (-w) = value w ∧ vector (-w) = (1, J (vector w).2) := by
  let t : W → W × (ℂ × E) :=
    fun w => (-w, (value w - energy, J (vector w).2))
  have ht : Tendsto t (𝓝 (0 : W)) (𝓝 ((0, 0) : W × (ℂ × E))) := by
    have hc : ContinuousAt t 0 :=
      continuousAt_neg.prodMk ((hv.sub continuousAt_const).prodMk
        (J.continuousAt.comp hu.snd))
    have ht0 : t 0 = (0, 0) := by simp [t, hv0, hu0]
    simpa only [ht0] using hc.tendsto
  filter_upwards [hsolve, ht.eventually hunique] with w hw huniq
  have hs : A (-w) (1, J (vector w).2) =
      (energy + (value w - energy)) • (1, J (vector w).2) := by
    have h := hsym w (vector w)
    rw [hnorm w, hw] at h
    simpa only [Prod.smul_fst, Prod.smul_snd, Prod.smul_mk, hnorm w, map_smul,
      add_sub_cancel, smul_eq_mul, mul_one] using h
  have hh := huniq.mp hs
  constructor
  · simpa [t] using hh.1
  · apply Prod.ext
    · exact hnorm (-w)
    · exact hh.2

omit [CompleteSpace W] [CompleteSpace E] [NormedSpace ℂ W] in
/-- Anti-linear covariance of the actual operator gives conjugation symmetry
of the constructed local branch by joint uniqueness. The parameter map may
be complex conjugation or negative complex conjugation. -/
theorem eigenpair_conjugation_of_local_uniqueness
    (A : W → (ℂ × E) →L[ℂ] (ℂ × E)) (energy : ℂ)
    (value : W → ℂ) (vector : W → ℂ × E) (ρ : W → W) (J : E → E)
    (hρ : ContinuousAt ρ 0) (hρ0 : ρ 0 = 0)
    (hJ : ContinuousAt J 0) (hJ0 : J 0 = 0)
    (hJsmul : ∀ (c : ℂ) (v : E), J (c • v) = starRingEnd ℂ c • J v)
    (henergy : starRingEnd ℂ energy = energy)
    (hv0 : value 0 = energy) (hu0 : vector 0 = (1, 0))
    (hv : ContinuousAt value 0) (hu : ContinuousAt vector 0)
    (hnorm : ∀ w, (vector w).1 = 1)
    (hsolve : ∀ᶠ w in 𝓝 (0 : W), A w (vector w) = value w • vector w)
    (hunique : ∀ᶠ z in 𝓝 ((0, 0) : W × (ℂ × E)),
      A z.1 (1, z.2.2) = (energy + z.2.1) • (1, z.2.2) ↔
        value z.1 = energy + z.2.1 ∧ (vector z.1).2 = z.2.2)
    (hsym : ∀ (w : W) (z : ℂ × E),
      A (ρ w) (starRingEnd ℂ z.1, J z.2) =
        (starRingEnd ℂ (A w z).1, J (A w z).2)) :
    ∀ᶠ w in 𝓝 (0 : W),
      value (ρ w) = starRingEnd ℂ (value w) ∧
      vector (ρ w) = (1, J (vector w).2) := by
  let t : W → W × (ℂ × E) :=
    fun w => (ρ w, (starRingEnd ℂ (value w) - energy, J (vector w).2))
  have ht : Tendsto t (𝓝 (0 : W)) (𝓝 ((0, 0) : W × (ℂ × E))) := by
    have hj : ContinuousAt (fun w => J (vector w).2) 0 :=
      hJ.comp_of_eq hu.snd (by simp [hu0])
    have hc : ContinuousAt t 0 :=
      hρ.prodMk (((continuousAt_star.comp hv).sub continuousAt_const).prodMk hj)
    have ht0 : t 0 = (0, 0) := by simp [t, hρ0, hv0, hu0, henergy, hJ0]
    simpa only [ht0] using hc.tendsto
  filter_upwards [hsolve, ht.eventually hunique] with w hw huniq
  have hs : A (ρ w) (1, J (vector w).2) =
      (energy + (starRingEnd ℂ (value w) - energy)) • (1, J (vector w).2) := by
    have h := hsym w (vector w)
    rw [hnorm w, hw] at h
    simpa only [map_one, Prod.smul_fst, Prod.smul_snd, Prod.smul_mk, hnorm w,
      hJsmul, add_sub_cancel, smul_eq_mul, mul_one] using h
  have hh := huniq.mp hs
  constructor
  · simpa [t] using hh.1
  · apply Prod.ext
    · exact hnorm (ρ w)
    · exact hh.2

section CoordinateTransport

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- A fixed change of coordinates acts continuously and linearly on operators.
Its construction contains no choice of an input-dependent eigenvector. -/
def coordinateConjugation (e : (ℂ × E) ≃L[ℂ] H) :
    (H →L[ℂ] H) →L[ℂ] ((ℂ × E) →L[ℂ] (ℂ × E)) :=
  (ContinuousLinearMap.compL ℂ (ℂ × E) H (ℂ × E)
    (e.symm : H →L[ℂ] (ℂ × E))).comp
    ((ContinuousLinearMap.compL ℂ (ℂ × E) H H).flip
      (e : (ℂ × E) →L[ℂ] H))

omit [CompleteSpace E] in
@[simp] theorem coordinateConjugation_apply
    (e : (ℂ × E) ≃L[ℂ] H) (T : H →L[ℂ] H) (z : ℂ × E) :
    coordinateConjugation e T z = e.symm (T (e z)) := rfl

/-- The constructed branch transports to any finite Hilbert-space operator
family after a fixed simple-eigenspace/complement decomposition at the center.
The complement may be an actual orthogonal-complement subspace; no analytic
choice of basis or eigenvector is an input. -/
theorem exists_analytic_eigenpair
    (A : W → H →L[ℂ] H) (energy : ℂ) (e : (ℂ × E) ≃L[ℂ] H)
    (B : E ≃L[ℂ] E) (hA : AnalyticAt ℂ A 0)
    (hcenter : ∀ z : ℂ × E,
      A 0 (e z) = e (energy * z.1, energy • z.2 + B z.2)) :
    ∃ value : W → ℂ, ∃ vector : W → H,
      value 0 = energy ∧ vector 0 = e (1, 0) ∧
      AnalyticAt ℂ value 0 ∧ AnalyticAt ℂ vector 0 ∧
      (∀ w, (e.symm (vector w)).1 = 1 ∧ vector w ≠ 0) ∧
      (∀ᶠ w in 𝓝 (0 : W), A w (vector w) = value w • vector w) := by
  let Ac : W → (ℂ × E) →L[ℂ] (ℂ × E) := fun w => coordinateConjugation e (A w)
  have hc : AnalyticAt ℂ Ac 0 := ((coordinateConjugation e).analyticAt (A 0)).comp hA
  have h0 (z : ℂ × E) : Ac 0 z = (energy * z.1, energy • z.2 + B z.2) := by
    change e.symm (A 0 (e z)) = _
    rw [hcenter]
    exact e.symm_apply_apply _
  obtain ⟨value, vector, hv0, hu0, hv, hu, hnorm, hsolve, _⟩ :=
    exists_analytic_normalized_eigenpair Ac energy B hc h0
  refine ⟨value, fun w => e (vector w), hv0, ?_, hv, ?_, ?_, ?_⟩
  · simp [hu0]
  · exact (e.analyticAt (vector 0)).comp hu
  · intro w
    refine ⟨by simpa using (hnorm w).1, ?_⟩
    intro hz
    apply (hnorm w).2
    exact e.injective (by simpa using hz)
  · filter_upwards [hsolve] with w hw
    apply e.symm.injective
    simpa only [Ac, coordinateConjugation_apply, map_smul, e.symm_apply_apply] using hw

/-- In finite dimension it suffices to prove that the shifted complementary
block has zero kernel. Its inverse is constructed, rather than supplied as
an extra analytic or computational oracle. This is the simple-eigenvalue
criterion in a fixed eigenspace/complement decomposition. -/
theorem exists_analytic_eigenpair_of_simple_complement [FiniteDimensional ℂ E]
    (A : W → H →L[ℂ] H) (energy : ℂ) (e : (ℂ × E) ≃L[ℂ] H)
    (D : E →L[ℂ] E) (hA : AnalyticAt ℂ A 0)
    (hcenter : ∀ z : ℂ × E,
      A 0 (e z) = e (energy * z.1, energy • z.2 + D z.2))
    (hsimple : ∀ v, D v = 0 → v = 0) :
    ∃ value : W → ℂ, ∃ vector : W → H,
      value 0 = energy ∧ vector 0 = e (1, 0) ∧
      AnalyticAt ℂ value 0 ∧ AnalyticAt ℂ vector 0 ∧
      (∀ w, (e.symm (vector w)).1 = 1 ∧ vector w ≠ 0) ∧
      (∀ᶠ w in 𝓝 (0 : W), A w (vector w) = value w • vector w) := by
  have hinj : Function.Injective D := by
    intro v w h
    apply sub_eq_zero.mp
    apply hsimple
    simp [map_sub, h]
  let B : E ≃L[ℂ] E :=
    (LinearEquiv.ofInjectiveEndo D.toLinearMap hinj).toContinuousLinearEquiv
  exact exists_analytic_eigenpair A energy e B hA hcenter

end CoordinateTransport

section AnalyticProjection

/-- The bordered normal operator of the normalized eigenpair equation. -/
def bordered (T : (ℂ × E) →L[ℂ] (ℂ × E)) (value : ℂ) (u : ℂ × E) :
    (ℂ × E) →L[ℂ] (ℂ × E) :=
  (T - value • 1) * ((ContinuousLinearMap.inr ℂ ℂ E).comp
    (ContinuousLinearMap.snd ℂ ℂ E)) - (ContinuousLinearMap.fst ℂ ℂ E).smulRight u

omit [CompleteSpace E] in
@[simp] theorem bordered_apply (T : (ℂ × E) →L[ℂ] (ℂ × E))
    (value : ℂ) (u z : ℂ × E) :
    bordered T value u z = (T - value • 1) (0, z.2) - z.1 • u := rfl

/-- A holomorphic left eigenfunctional comes from the inverse bordered
operator, rather than conjugating a holomorphic right eigenvector. -/
def leftFunctional (T : (ℂ × E) →L[ℂ] (ℂ × E)) (value : ℂ) (u : ℂ × E) :
    (ℂ × E) →L[ℂ] ℂ :=
  -((ContinuousLinearMap.fst ℂ ℂ E).comp (bordered T value u).inverse)

def eigenprojection (T : (ℂ × E) →L[ℂ] (ℂ × E)) (value : ℂ) (u : ℂ × E) :
    (ℂ × E) →L[ℂ] (ℂ × E) :=
  (leftFunctional T value u).smulRight u

omit [CompleteSpace E] in
theorem leftFunctional_apply (T : (ℂ × E) →L[ℂ] (ℂ × E))
    (value : ℂ) (u x : ℂ × E) :
    leftFunctional T value u x = -((bordered T value u).inverse x).1 := rfl

omit [CompleteSpace E] in
theorem eigenprojection_apply (T : (ℂ × E) →L[ℂ] (ℂ × E))
    (value : ℂ) (u x : ℂ × E) :
    eigenprojection T value u x = leftFunctional T value u x • u := rfl

omit [CompleteSpace E] in
theorem leftFunctional_vector (T : (ℂ × E) →L[ℂ] (ℂ × E))
    (value : ℂ) (u : ℂ × E) (hi : (bordered T value u).IsInvertible) :
    leftFunctional T value u u = 1 := by
  have h : (bordered T value u).inverse u = (-1, 0) := by
    apply hi.inverse_apply_eq.mpr
    rw [bordered_apply]
    change u = (T - value • 1) 0 - (-1 : ℂ) • u
    simp
  rw [leftFunctional_apply, h]
  simp

omit [CompleteSpace E] in
theorem leftFunctional_shift (T : (ℂ × E) →L[ℂ] (ℂ × E))
    (value : ℂ) (u : ℂ × E) (hnorm : u.1 = 1) (heigen : T u = value • u)
    (hi : (bordered T value u).IsInvertible) (x : ℂ × E) :
    leftFunctional T value u ((T - value • 1) x) = 0 := by
  have hu : (T - value • 1) u = 0 := by simp [heigen]
  have hx : x = x.1 • u + (0, x.2 - x.1 • u.2) := by
    apply Prod.ext <;> simp [hnorm]
  have h : (bordered T value u).inverse ((T - value • 1) x) =
      (0, x.2 - x.1 • u.2) := by
    apply hi.inverse_apply_eq.mpr
    rw [bordered_apply]
    simp only [zero_smul, sub_zero]
    conv_lhs => rw [hx]
    rw [map_add, map_smul, hu, smul_zero, zero_add]
  rw [leftFunctional_apply, h]
  simp

omit [CompleteSpace E] in
theorem leftFunctional_eigen (T : (ℂ × E) →L[ℂ] (ℂ × E))
    (value : ℂ) (u : ℂ × E) (hnorm : u.1 = 1) (heigen : T u = value • u)
    (hi : (bordered T value u).IsInvertible) (x : ℂ × E) :
    leftFunctional T value u (T x) = value * leftFunctional T value u x := by
  have h := leftFunctional_shift T value u hnorm heigen hi x
  simpa only [sub_apply, smul_apply,
    one_apply_eq_self, map_sub, map_smul, smul_eq_mul, sub_eq_zero] using h

omit [CompleteSpace E] in
theorem eigenprojection_idempotent (T : (ℂ × E) →L[ℂ] (ℂ × E))
    (value : ℂ) (u : ℂ × E) (hi : (bordered T value u).IsInvertible) :
    eigenprojection T value u * eigenprojection T value u = eigenprojection T value u := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [mul_apply_eq_comp, eigenprojection_apply, map_smul,
    leftFunctional_vector T value u hi, one_smul]

omit [CompleteSpace E] in
theorem eigenprojection_right (T : (ℂ × E) →L[ℂ] (ℂ × E))
    (value : ℂ) (u : ℂ × E) (heigen : T u = value • u) :
    T * eigenprojection T value u = value • eigenprojection T value u := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [mul_apply_eq_comp, eigenprojection_apply, map_smul,
    heigen, smul_apply]
  exact smul_comm _ _ _

omit [CompleteSpace E] in
theorem eigenprojection_left (T : (ℂ × E) →L[ℂ] (ℂ × E))
    (value : ℂ) (u : ℂ × E) (hnorm : u.1 = 1) (heigen : T u = value • u)
    (hi : (bordered T value u).IsInvertible) :
    eigenprojection T value u * T = value • eigenprojection T value u := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [mul_apply_eq_comp, eigenprojection_apply,
    smul_apply, leftFunctional_eigen T value u hnorm heigen hi,
    mul_smul]

omit [CompleteSpace W] in
theorem analyticAt_operator_inverse {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (L : W → F →L[ℂ] F) (hL : AnalyticAt ℂ L 0) (hi : (L 0).IsInvertible) :
    AnalyticAt ℂ (fun w => (L w).inverse) 0 := by
  obtain ⟨B, hB⟩ := hi
  have ha : AnalyticAt ℂ (ContinuousLinearMap.inverse (R := ℂ) (M := F)) (L 0) := by
    rw [← hB, ← ContinuousLinearMap.ringInverse_eq_inverse]
    exact analyticAt_inverse B.toUnit
  exact ha.comp hL

omit [CompleteSpace W] [CompleteSpace E] in
theorem bordered_analytic
    (A : W → (ℂ × E) →L[ℂ] (ℂ × E)) (value : W → ℂ) (u : W → ℂ × E)
    (hA : AnalyticAt ℂ A 0) (hv : AnalyticAt ℂ value 0) (hu : AnalyticAt ℂ u 0) :
    AnalyticAt ℂ (fun w => bordered (A w) (value w) (u w)) 0 := by
  have hr : AnalyticAt ℂ
      (fun w => (ContinuousLinearMap.fst ℂ ℂ E).smulRight (u w)) 0 :=
    ((ContinuousLinearMap.smulRightL ℂ (ℂ × E) (ℂ × E)
      (ContinuousLinearMap.fst ℂ ℂ E)).analyticAt (u 0)).comp hu
  exact ((hA.sub (hv.smul analyticAt_const)).mul analyticAt_const).sub hr

omit [CompleteSpace E] in
theorem bordered_center
    (A : (ℂ × E) →L[ℂ] (ℂ × E)) (energy : ℂ) (B : E ≃L[ℂ] E)
    (hcenter : ∀ z : ℂ × E, A z = (energy * z.1, energy • z.2 + B z.2)) :
    bordered A energy (1, 0) = (normalEquiv B : (ℂ × E) →L[ℂ] (ℂ × E)) := by
  apply ContinuousLinearMap.ext
  intro z
  apply Prod.ext <;> simp [hcenter, normalEquiv]

omit [CompleteSpace W] in
theorem eigenprojection_analytic
    (A : W → (ℂ × E) →L[ℂ] (ℂ × E)) (value : W → ℂ) (u : W → ℂ × E)
    (hA : AnalyticAt ℂ A 0) (hv : AnalyticAt ℂ value 0) (hu : AnalyticAt ℂ u 0)
    (hi : (bordered (A 0) (value 0) (u 0)).IsInvertible) :
    AnalyticAt ℂ (fun w => eigenprojection (A w) (value w) (u w)) 0 := by
  have hinv := analyticAt_operator_inverse _ (bordered_analytic A value u hA hv hu) hi
  have hl : AnalyticAt ℂ (fun w => leftFunctional (A w) (value w) (u w)) 0 :=
    (((ContinuousLinearMap.compL ℂ (ℂ × E) (ℂ × E) ℂ
      (ContinuousLinearMap.fst ℂ ℂ E)).analyticAt _).comp hinv).neg
  exact ((ContinuousLinearMap.smulRightL ℂ (ℂ × E) (ℂ × E)).analyticAt_bilinear _).comp₂ hl hu

omit [CompleteSpace E] in
theorem eigenprojection_range (T : (ℂ × E) →L[ℂ] (ℂ × E))
    (value : ℂ) (u : ℂ × E) (hi : (bordered T value u).IsInvertible) :
    LinearMap.range (eigenprojection T value u).toLinearMap =
      Submodule.span ℂ ({u} : Set (ℂ × E)) := by
  apply le_antisymm
  · rintro x ⟨y, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton u))
  · apply Submodule.span_le.mpr
    intro x hx
    have hx' : x = u := Set.mem_singleton_iff.mp hx
    subst x
    refine ⟨u, ?_⟩
    simp only [ContinuousLinearMap.coe_coe, eigenprojection_apply,
      leftFunctional_vector T value u hi, one_smul]

omit [CompleteSpace E] in
theorem eigenprojection_center
    (T : (ℂ × E) →L[ℂ] (ℂ × E)) (energy : ℂ) (B : E ≃L[ℂ] E)
    (hcenter : ∀ z : ℂ × E, T z = (energy * z.1, energy • z.2 + B z.2)) :
    eigenprojection T energy (1, 0) =
      (ContinuousLinearMap.fst ℂ ℂ E).smulRight (1, 0) := by
  apply ContinuousLinearMap.ext
  intro z
  rw [eigenprojection_apply, leftFunctional_apply, bordered_center T energy B hcenter]
  rw [ContinuousLinearMap.inverse_equiv]
  simp [normalEquiv]

/-- A rank-one spectral projection is constructed jointly with the analytic
eigenbranch. Its identities hold on one common neighborhood and refer to the
actual input operator family. No projection, branch or holomorphic dual
eigenvector appears among the hypotheses. -/
theorem exists_analytic_eigenprojection_with_uniqueness
    (A : W → (ℂ × E) →L[ℂ] (ℂ × E)) (energy : ℂ) (B : E ≃L[ℂ] E)
    (hA : AnalyticAt ℂ A 0)
    (hcenter : ∀ z : ℂ × E, A 0 z = (energy * z.1, energy • z.2 + B z.2)) :
    ∃ value : W → ℂ, ∃ u : W → ℂ × E,
    ∃ P : W → (ℂ × E) →L[ℂ] (ℂ × E),
      value 0 = energy ∧ u 0 = (1, 0) ∧
      P 0 = (ContinuousLinearMap.fst ℂ ℂ E).smulRight (1, 0) ∧
      AnalyticAt ℂ value 0 ∧ AnalyticAt ℂ u 0 ∧ AnalyticAt ℂ P 0 ∧
      (∀ w, (u w).1 = 1 ∧ u w ≠ 0) ∧
      (∀ᶠ w in 𝓝 (0 : W),
        A w (u w) = value w • u w ∧
        P w * P w = P w ∧
        A w * P w = value w • P w ∧ P w * A w = value w • P w ∧
        LinearMap.range (P w).toLinearMap = Submodule.span ℂ ({u w} : Set (ℂ × E))) ∧
      (∀ᶠ z in 𝓝 ((0, 0) : W × (ℂ × E)),
        A z.1 (1, z.2.2) = (energy + z.2.1) • (1, z.2.2) ↔
          value z.1 = energy + z.2.1 ∧ (u z.1).2 = z.2.2) := by
  obtain ⟨value, u, hv0, hu0, hv, hu, hnorm, hsolve, hunique⟩ :=
    exists_analytic_normalized_eigenpair A energy B hA hcenter
  let P := fun w => eigenprojection (A w) (value w) (u w)
  have hi0 : (bordered (A 0) (value 0) (u 0)).IsInvertible := by
    rw [hv0, hu0, bordered_center (A 0) energy B hcenter]
    exact ContinuousLinearMap.isInvertible_equiv
  have ha := bordered_analytic A value u hA hv hu
  have hi : ∀ᶠ w in 𝓝 (0 : W), (bordered (A w) (value w) (u w)).IsInvertible :=
    ha.continuousAt.tendsto.eventually hi0.eventually_nhds
  refine ⟨value, u, P, hv0, hu0, ?_, hv, hu,
    eigenprojection_analytic A value u hA hv hu hi0, hnorm, ?_, hunique⟩
  · dsimp [P]
    rw [hv0, hu0]
    exact eigenprojection_center (A 0) energy B hcenter
  · filter_upwards [hsolve, hi] with w hw hwi
    exact ⟨hw, eigenprojection_idempotent _ _ _ hwi,
      eigenprojection_right _ _ _ hw,
      eigenprojection_left _ _ _ (hnorm w).1 hw hwi,
      eigenprojection_range _ _ _ hwi⟩

/-- The spectral projector exists without any prescribed branch. -/
theorem exists_analytic_eigenprojection
    (A : W → (ℂ × E) →L[ℂ] (ℂ × E)) (energy : ℂ) (B : E ≃L[ℂ] E)
    (hA : AnalyticAt ℂ A 0)
    (hcenter : ∀ z : ℂ × E, A 0 z = (energy * z.1, energy • z.2 + B z.2)) :
    ∃ value : W → ℂ, ∃ u : W → ℂ × E,
    ∃ P : W → (ℂ × E) →L[ℂ] (ℂ × E),
      value 0 = energy ∧ u 0 = (1, 0) ∧
      P 0 = (ContinuousLinearMap.fst ℂ ℂ E).smulRight (1, 0) ∧
      AnalyticAt ℂ value 0 ∧ AnalyticAt ℂ u 0 ∧ AnalyticAt ℂ P 0 ∧
      (∀ w, (u w).1 = 1 ∧ u w ≠ 0) ∧
      (∀ᶠ w in 𝓝 (0 : W),
        A w (u w) = value w • u w ∧ P w * P w = P w ∧
        A w * P w = value w • P w ∧ P w * A w = value w • P w ∧
        LinearMap.range (P w).toLinearMap = Submodule.span ℂ ({u w} : Set (ℂ × E))) := by
  obtain ⟨value, u, P, hv0, hu0, hP0, hv, hu, hP, hnorm, hgood, _⟩ :=
    exists_analytic_eigenprojection_with_uniqueness A energy B hA hcenter
  exact ⟨value, u, P, hv0, hu0, hP0, hv, hu, hP, hnorm, hgood⟩

end AnalyticProjection

section RegularResolvent

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The complementary resolvent is regular even where the isolated scalar
eigenvalue denominator vanishes. The inverse here is taken after adding the
eigenprojection, which opens that one-dimensional singular direction. -/
def regularResolvent (T P : F →L[ℂ] F) (spectral : ℂ) : F →L[ℂ] F :=
  (1 - P) * (T - spectral • 1 + P).inverse * (1 - P)

/-- Exact two-sided resolvent decomposition from the proved spectral
projection identities. Invertibility of the full shifted matrix is a
conclusion; only the regular augmented matrix is required to be invertible. -/
theorem inverse_eq_pole_add_regular
    (T P : F →L[ℂ] F) (value spectral : ℂ)
    (hPP : P * P = P) (hTP : T * P = value • P) (hPT : P * T = value • P)
    (hi : (T - spectral • 1 + P).IsInvertible) (hne : value - spectral ≠ 0) :
    (T - spectral • 1).IsInvertible ∧
    (T - spectral • 1).inverse =
      (value - spectral)⁻¹ • P + regularResolvent T P spectral := by
  let S := T - spectral • (1 : F →L[ℂ] F)
  let K := S + P
  let Q := (1 : F →L[ℂ] F) - P
  let R := Q * K.inverse * Q
  have hSP : S * P = (value - spectral) • P := by
    dsimp [S]
    rw [sub_mul, smul_mul_assoc, one_mul, hTP, sub_smul]
  have hPS : P * S = (value - spectral) • P := by
    dsimp [S]
    rw [mul_sub, mul_smul_comm, mul_one, hPT, sub_smul]
  have hQP : Q * P = 0 := by
    dsimp [Q]
    rw [sub_mul, one_mul, hPP, sub_self]
  have hPQ : P * Q = 0 := by
    dsimp [Q]
    rw [mul_sub, mul_one, hPP, sub_self]
  have hQQ : Q * Q = Q := by
    dsimp [Q]
    rw [mul_sub, mul_one, sub_mul, one_mul, hPP, sub_self, sub_zero]
  have hSQ : S * Q = Q * S := by
    change S * (1 - P) = (1 - P) * S
    rw [mul_sub S 1 P, sub_mul 1 P S, mul_one, one_mul, hSP, hPS]
  have hKI : K * K.inverse = 1 := hi.self_comp_inverse
  have hIK : K.inverse * K = 1 := hi.inverse_comp_self
  have hSK : S = K - P := by dsimp [K]; abel
  have hSR : S * R = Q := by
    calc
      S * R = Q * (S * K.inverse) * Q := by
        dsimp [R]
        rw [← mul_assoc S, ← mul_assoc S, hSQ]
        simp only [mul_assoc]
      _ = Q * (1 - P * K.inverse) * Q := by
        rw [hSK, sub_mul K P K.inverse, hKI]
      _ = Q := by rw [mul_sub Q 1 (P * K.inverse), mul_one,
        ← mul_assoc Q P K.inverse, hQP, zero_mul,
        sub_zero, hQQ]
  have hRS : R * S = Q := by
    calc
      R * S = Q * (K.inverse * S) * Q := by
        dsimp [R]
        rw [mul_assoc, ← hSQ]
        simp only [mul_assoc]
      _ = Q * (1 - K.inverse * P) * Q := by
        rw [hSK, mul_sub K.inverse K P, hIK]
      _ = Q := by
        rw [mul_assoc Q (1 - K.inverse * P) Q,
          sub_mul 1 (K.inverse * P) Q, one_mul, mul_assoc K.inverse P Q, hPQ, mul_zero,
          sub_zero, hQQ]
  have hleft : S * ((value - spectral)⁻¹ • P + R) = 1 := by
    rw [mul_add, mul_smul_comm, hSP, smul_smul, inv_mul_cancel₀ hne, one_smul, hSR]
    dsimp [Q]
    abel
  have hright : ((value - spectral)⁻¹ • P + R) * S = 1 := by
    rw [add_mul, smul_mul_assoc, hPS, smul_smul, inv_mul_cancel₀ hne, one_smul, hRS]
    dsimp [Q]
    abel
  exact ⟨ContinuousLinearMap.IsInvertible.of_inverse hleft hright,
    ContinuousLinearMap.inverse_eq hleft hright⟩

omit [CompleteSpace W] in
theorem regularResolvent_analytic [CompleteSpace F]
    (A P : W → F →L[ℂ] F) (energy : ℂ)
    (hA : AnalyticAt ℂ A 0) (hP : AnalyticAt ℂ P 0)
    (hi : (A 0 - energy • 1 + P 0).IsInvertible) :
    AnalyticAt ℂ (fun z : W × ℂ => regularResolvent (A z.1) (P z.1) (energy + z.2))
      (0, 0) := by
  have ha : AnalyticAt ℂ (fun z : W × ℂ => A z.1) (0, 0) :=
    hA.comp_of_eq analyticAt_fst rfl
  have hp : AnalyticAt ℂ (fun z : W × ℂ => P z.1) (0, 0) :=
    hP.comp_of_eq analyticAt_fst rfl
  have he : AnalyticAt ℂ (fun z : W × ℂ => energy + z.2) (0, 0) :=
    analyticAt_const.add analyticAt_snd
  have hk : AnalyticAt ℂ
      (fun z : W × ℂ => A z.1 - (energy + z.2) • 1 + P z.1) (0, 0) :=
    (ha.sub (he.smul analyticAt_const)).add hp
  have hi' : (A 0 - (energy + (0 : ℂ)) • 1 + P 0).IsInvertible := by simpa using hi
  have hInv := analyticAt_operator_inverse
    (fun z : W × ℂ => A z.1 - (energy + z.2) • 1 + P z.1) hk hi'
  exact ((analyticAt_const.sub hp).mul hInv).mul (analyticAt_const.sub hp)

omit [CompleteSpace E] in
omit [CompleteSpace W] in
/-- Extend a fixed constructed eigenbranch and projector to a regular
resolvent. This preserves the witnesses used for symmetry and derivative
arguments, instead of choosing a second unrelated branch. -/
theorem regular_resolvent_near_eigenprojection [CompleteSpace F]
    (A : W → F →L[ℂ] F) (value : W → ℂ) (P : W → F →L[ℂ] F) (energy : ℂ)
    (hA : AnalyticAt ℂ A 0) (hP : AnalyticAt ℂ P 0)
    (hi0 : (A 0 - energy • 1 + P 0).IsInvertible)
    (hgood : ∀ᶠ w in 𝓝 (0 : W),
      P w * P w = P w ∧ A w * P w = value w • P w ∧
      P w * A w = value w • P w) :
    AnalyticAt ℂ (fun z : W × ℂ => regularResolvent (A z.1) (P z.1)
      (energy + z.2)) (0, 0) ∧
    (∀ᶠ z in 𝓝 ((0, 0) : W × ℂ), value z.1 ≠ energy + z.2 →
      (A z.1 - (energy + z.2) • 1).IsInvertible ∧
      (A z.1 - (energy + z.2) • 1).inverse =
        (value z.1 - (energy + z.2))⁻¹ • P z.1 +
          regularResolvent (A z.1) (P z.1) (energy + z.2)) := by
  refine ⟨regularResolvent_analytic A P energy hA hP hi0, ?_⟩
  have ha : AnalyticAt ℂ (fun z : W × ℂ => A z.1) (0, 0) :=
    hA.comp_of_eq analyticAt_fst rfl
  have hp : AnalyticAt ℂ (fun z : W × ℂ => P z.1) (0, 0) :=
    hP.comp_of_eq analyticAt_fst rfl
  have he : AnalyticAt ℂ (fun z : W × ℂ => energy + z.2) (0, 0) :=
    analyticAt_const.add analyticAt_snd
  have hk : AnalyticAt ℂ
      (fun z : W × ℂ => A z.1 - (energy + z.2) • 1 + P z.1) (0, 0) :=
    (ha.sub (he.smul analyticAt_const)).add hp
  have hi0' : (A 0 - (energy + (0 : ℂ)) • 1 + P 0).IsInvertible := by simpa using hi0
  have hi : ∀ᶠ z : W × ℂ in 𝓝 (0, 0),
      (A z.1 - (energy + z.2) • 1 + P z.1).IsInvertible :=
    hk.continuousAt.tendsto.eventually hi0'.eventually_nhds
  have hf : Tendsto (fun z : W × ℂ => z.1) (𝓝 (0, 0)) (𝓝 (0 : W)) :=
    continuousAt_fst.tendsto
  filter_upwards [hi, hf.eventually hgood] with z hz hg
  intro hne
  exact inverse_eq_pole_add_regular _ _ _ _ hg.1 hg.2.1 hg.2.2 hz (sub_ne_zero.mpr hne)

omit [CompleteSpace E] in
theorem augmented_center_invertible
    (T : (ℂ × E) →L[ℂ] (ℂ × E)) (energy : ℂ) (B : E ≃L[ℂ] E)
    (hcenter : ∀ z : ℂ × E, T z = (energy * z.1, energy • z.2 + B z.2)) :
    (T - energy • 1 + (ContinuousLinearMap.fst ℂ ℂ E).smulRight (1, 0)).IsInvertible := by
  let J := (ContinuousLinearEquiv.refl ℂ ℂ).prodCongr B
  refine ⟨J, ?_⟩
  apply ContinuousLinearMap.ext
  intro z
  apply Prod.ext <;> simp [J, hcenter]

/-- Complete local spectral data and a jointly analytic regular resolvent
are constructed from a simple center block. The two-sided full inverse and
its pole decomposition hold at every nearby off-pole complex parameter. -/
theorem exists_analytic_resolvent_decomposition
    (A : W → (ℂ × E) →L[ℂ] (ℂ × E)) (energy : ℂ) (B : E ≃L[ℂ] E)
    (hA : AnalyticAt ℂ A 0)
    (hcenter : ∀ z : ℂ × E, A 0 z = (energy * z.1, energy • z.2 + B z.2)) :
    ∃ value : W → ℂ, ∃ P : W → (ℂ × E) →L[ℂ] (ℂ × E),
    ∃ R : W × ℂ → (ℂ × E) →L[ℂ] (ℂ × E),
      value 0 = energy ∧
      P 0 = (ContinuousLinearMap.fst ℂ ℂ E).smulRight (1, 0) ∧
      AnalyticAt ℂ value 0 ∧ AnalyticAt ℂ P 0 ∧ AnalyticAt ℂ R (0, 0) ∧
      (∀ᶠ w in 𝓝 (0 : W),
        P w * P w = P w ∧ A w * P w = value w • P w ∧
        P w * A w = value w • P w) ∧
      (∀ᶠ z in 𝓝 ((0, 0) : W × ℂ), value z.1 ≠ energy + z.2 →
        (A z.1 - (energy + z.2) • 1).IsInvertible ∧
        (A z.1 - (energy + z.2) • 1).inverse =
          (value z.1 - (energy + z.2))⁻¹ • P z.1 + R z) := by
  obtain ⟨value, _u, P, hv0, _hu0, hP0, hv, _hu, hP, _hnorm, hgood⟩ :=
    exists_analytic_eigenprojection A energy B hA hcenter
  let R := fun z : W × ℂ => regularResolvent (A z.1) (P z.1) (energy + z.2)
  have hi0 : (A 0 - energy • 1 + P 0).IsInvertible := by
    rw [hP0]
    exact augmented_center_invertible (A 0) energy B hcenter
  have hg : ∀ᶠ w in 𝓝 (0 : W),
      P w * P w = P w ∧ A w * P w = value w • P w ∧
      P w * A w = value w • P w := by
    filter_upwards [hgood] with w hw
    exact ⟨hw.2.1, hw.2.2.1, hw.2.2.2.1⟩
  obtain ⟨hR, hres⟩ := regular_resolvent_near_eigenprojection A value P energy hA hP hi0 hg
  exact ⟨value, P, R, hv0, hP0, hv, hP, hR, hg, hres⟩

end RegularResolvent

section ResolventTransport

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace E] [CompleteSpace H] in
theorem conjugation_inverse (e : (ℂ × E) ≃L[ℂ] H)
    (T : (ℂ × E) →L[ℂ] (ℂ × E)) :
    (e.conjContinuousAlgEquiv T).inverse = e.conjContinuousAlgEquiv T.inverse := by
  simp only [ContinuousLinearEquiv.conjContinuousAlgEquiv_apply,
    ContinuousLinearMap.inverse_equiv_comp, ContinuousLinearMap.inverse_comp_equiv,
    ContinuousLinearEquiv.symm_symm, ContinuousLinearMap.comp_assoc]

omit [CompleteSpace E] [CompleteSpace H] in
theorem conjugation_isInvertible (e : (ℂ × E) ≃L[ℂ] H)
    (T : (ℂ × E) →L[ℂ] (ℂ × E)) :
    (e.conjContinuousAlgEquiv T).IsInvertible ↔ T.IsInvertible := by
  simp only [ContinuousLinearEquiv.conjContinuousAlgEquiv_apply,
    ContinuousLinearMap.isInvertible_equiv_comp, ContinuousLinearMap.isInvertible_comp_equiv]

omit [CompleteSpace H] in
/-- The constructed spectral projector and actual resolvent decomposition
transport to the physical space by a fixed continuous coordinate change. -/
theorem exists_analytic_resolvent_decomposition_in_coordinates
    (A : W → H →L[ℂ] H) (energy : ℂ)
    (e : (ℂ × E) ≃L[ℂ] H) (B : E ≃L[ℂ] E)
    (hA : AnalyticAt ℂ A 0)
    (hcenter : ∀ z : ℂ × E,
      A 0 (e z) = e (energy * z.1, energy • z.2 + B z.2)) :
    ∃ value : W → ℂ, ∃ P : W → H →L[ℂ] H,
    ∃ R : W × ℂ → H →L[ℂ] H,
      value 0 = energy ∧
      P 0 = e.conjContinuousAlgEquiv
        ((ContinuousLinearMap.fst ℂ ℂ E).smulRight (1, 0)) ∧
      AnalyticAt ℂ value 0 ∧ AnalyticAt ℂ P 0 ∧ AnalyticAt ℂ R (0, 0) ∧
      (∀ᶠ w in 𝓝 (0 : W),
        P w * P w = P w ∧ A w * P w = value w • P w ∧
        P w * A w = value w • P w) ∧
      (∀ᶠ z in 𝓝 ((0, 0) : W × ℂ), value z.1 ≠ energy + z.2 →
        (A z.1 - (energy + z.2) • 1).IsInvertible ∧
        (A z.1 - (energy + z.2) • 1).inverse =
          (value z.1 - (energy + z.2))⁻¹ • P z.1 + R z) := by
  let g := e.conjContinuousAlgEquiv
  let Ac := fun w => g.symm (A w)
  have hc : AnalyticAt ℂ Ac 0 :=
    (g.symm.toContinuousLinearEquiv.analyticAt (A 0)).comp hA
  have h0 (z : ℂ × E) : Ac 0 z = (energy * z.1, energy • z.2 + B z.2) := by
    change e.symm (A 0 (e z)) = _
    rw [hcenter]
    exact e.symm_apply_apply _
  obtain ⟨value, P, R, hv0, hP0, hv, hP, hR, hgood, hres⟩ :=
    exists_analytic_resolvent_decomposition Ac energy B hc h0
  refine ⟨value, fun w => g (P w), fun z => g (R z), hv0, ?_, hv, ?_, ?_, ?_, ?_⟩
  · exact congrArg g hP0
  · exact (g.toContinuousLinearEquiv.analyticAt (P 0)).comp hP
  · exact (g.toContinuousLinearEquiv.analyticAt (R (0, 0))).comp hR
  · filter_upwards [hgood] with w hw
    refine ⟨?_, ?_, ?_⟩
    · simpa only [map_mul] using congrArg g hw.1
    · simpa [Ac] using congrArg g hw.2.1
    · simpa [Ac] using congrArg g hw.2.2
  · filter_upwards [hres] with z hz
    intro hne
    obtain ⟨hi, heq⟩ := hz hne
    have hconj : g (Ac z.1 - (energy + z.2) • 1) =
        A z.1 - (energy + z.2) • 1 := by simp [Ac]
    refine ⟨?_, ?_⟩
    · rw [← hconj]
      exact (conjugation_isInvertible e _).mpr hi
    · have heq' := congrArg g heq
      rw [← conjugation_inverse e, hconj] at heq'
      simpa only [map_add, map_smul] using heq'

end ResolventTransport

section FiniteHermitian

variable {ι H : Type*} [Fintype ι] [DecidableEq ι]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]

omit [FiniteDimensional ℂ H] in
theorem spectral_first_projection (b : OrthonormalBasis ι ℂ H) (i : ι) :
    (SimpleSplitting.decomposition b i).conjContinuousAlgEquiv
      ((ContinuousLinearMap.fst ℂ ℂ (SimpleSplitting.Complement i)).smulRight (1, 0)) =
        (innerSL ℂ (b i)).smulRight (b i) := by
  apply ContinuousLinearMap.ext
  intro x
  change SimpleSplitting.decomposition b i
    (((SimpleSplitting.decomposition b i).symm x).1 • (1, 0)) =
      inner ℂ (b i) x • b i
  rw [map_smul, SimpleSplitting.decomposition_one_zero,
    SimpleSplitting.decomposition_symm_fst]

/-- A finite Hermitian simple eigenvalue supplies every center coordinate
and complementary inverse needed by the analytic construction. The only
spectral assumption is simplicity of the actual center eigenvalue. -/
theorem exists_analytic_resolvent_of_hermitian_simple
    (A : W → H →L[ℂ] H) (hA : AnalyticAt ℂ A 0)
    (hT : (A 0).toLinearMap.IsSymmetric)
    (i : Fin (Module.finrank ℂ H))
    (hsimple : ∀ j, j ≠ i → hT.eigenvalues rfl j ≠ hT.eigenvalues rfl i) :
    ∃ value : W → ℂ, ∃ P : W → H →L[ℂ] H,
    ∃ R : W × ℂ → H →L[ℂ] H,
      value 0 = (hT.eigenvalues rfl i : ℂ) ∧
      P 0 = (innerSL ℂ (hT.eigenvectorBasis rfl i)).smulRight
        (hT.eigenvectorBasis rfl i) ∧
      AnalyticAt ℂ value 0 ∧ AnalyticAt ℂ P 0 ∧ AnalyticAt ℂ R (0, 0) ∧
      (∀ᶠ w in 𝓝 (0 : W),
        P w * P w = P w ∧ A w * P w = value w • P w ∧
        P w * A w = value w • P w) ∧
      (∀ᶠ z in 𝓝 ((0, 0) : W × ℂ), value z.1 ≠ (hT.eigenvalues rfl i : ℂ) + z.2 →
        (A z.1 - ((hT.eigenvalues rfl i : ℂ) + z.2) • 1).IsInvertible ∧
        (A z.1 - ((hT.eigenvalues rfl i : ℂ) + z.2) • 1).inverse =
          (value z.1 - ((hT.eigenvalues rfl i : ℂ) + z.2))⁻¹ • P z.1 + R z) := by
  let e := SimpleSplitting.decomposition (hT.eigenvectorBasis rfl) i
  let B := SimpleSplitting.complementaryEquiv (hT.eigenvalues rfl) i hsimple
  have hc (z : ℂ × SimpleSplitting.Complement i) :
      A 0 (e z) = e ((hT.eigenvalues rfl i : ℂ) * z.1,
        (hT.eigenvalues rfl i : ℂ) • z.2 + B z.2) :=
    SimpleSplitting.spectral_decomposition (A 0).toLinearMap hT i z
  obtain ⟨value, P, R, hv0, hP0, hv, hP, hR, hgood, hres⟩ :=
    exists_analytic_resolvent_decomposition_in_coordinates A
      (hT.eigenvalues rfl i : ℂ) e B hA hc
  refine ⟨value, P, R, hv0, ?_, hv, hP, hR, hgood, hres⟩
  rw [hP0]
  exact spectral_first_projection (hT.eigenvectorBasis rfl) i

end FiniteHermitian

end Maxwell.Spectral.AnalyticEigenbranch
