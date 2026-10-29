import Maxwell.Certificate.FourierGauge
import Maxwell.Spectral.LowHighInertia

/-! Exact longitudinal and transverse coordinates of the primitive Fourier
curl. The low and high frequency spaces retain their actual finite dimensions. -/

noncomputable section

namespace Maxwell.Certificate.FourierBinding

open Matrix Maxwell.Spectral.PrimitiveYee
open Maxwell.Spectral.PeriodicYee (Direction Momentum)
open scoped ComplexConjugate

abbrev Polarization := EuclideanSpace ℂ Direction

/-- Squared norm of the actual difference symbol. -/
def laplacianSymbol (c : Momentum) (f : Frequency) : ℝ :=
  ∑ j, Complex.normSq (symbol c f j)

def longitudinalVector (c : Momentum) (f : Frequency) : Polarization :=
  WithLp.toLp 2 fun j => conj (symbol c f j)

/-- Magnetic transversality uses `dᵀ x = 0`, since the longitudinal vector is
`conj d`, the kernel vector of the adjoint curl. -/
def divergenceSymbol (c : Momentum) (f : Frequency) : Polarization →ₗ[ℂ] ℂ where
  toFun x := ∑ j, symbol c f j * x j
  map_add' x y := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' a x := by
    simp only [PiLp.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]
    apply Finset.sum_congr rfl
    intro j _
    ring

def transversePolarization (c : Momentum) (f : Frequency) : Submodule ℂ Polarization :=
  (divergenceSymbol c f).ker

theorem divergence_longitudinal (c : Momentum) (f : Frequency) :
    divergenceSymbol c f (longitudinalVector c f) = (laplacianSymbol c f : ℂ) := by
  change (∑ j, symbol c f j * conj (symbol c f j)) = _
  simp only [Complex.mul_conj, laplacianSymbol, Complex.ofReal_sum]

theorem longitudinal_inner (c : Momentum) (f : Frequency) (x : Polarization) :
    inner ℂ (longitudinalVector c f) x = divergenceSymbol c f x := by
  change (∑ j, x j * conj (conj (symbol c f j))) = ∑ j, symbol c f j * x j
  simp only [Complex.conj_conj]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

theorem transverse_eq_orthogonal (c : Momentum) (f : Frequency) :
    transversePolarization c f = (ℂ ∙ longitudinalVector c f)ᗮ := by
  ext x
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right, longitudinal_inner]
  rfl

theorem divergence_surjective (c : Momentum) (f : Frequency)
    (hlap : laplacianSymbol c f ≠ 0) : Function.Surjective (divergenceSymbol c f) := by
  intro z
  refine ⟨(z / (laplacianSymbol c f : ℂ)) • longitudinalVector c f, ?_⟩
  rw [map_smul, divergence_longitudinal, smul_eq_mul]
  exact div_mul_cancel₀ z (Complex.ofReal_ne_zero.mpr hlap)

theorem transversePolarization_finrank (c : Momentum) (f : Frequency)
    (hlap : laplacianSymbol c f ≠ 0) :
    Module.finrank ℂ (transversePolarization c f) = 2 := by
  have h := (divergenceSymbol c f).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (divergence_surjective c f hlap)] at h
  simp only [finrank_top, Module.finrank_self, finrank_euclideanSpace,
    Fintype.card_fin] at h
  change Module.finrank ℂ (divergenceSymbol c f).ker = 2
  omega

/-- The exact per-frequency gradient projection used by the certificate. -/
def gradientProjection (c : Momentum) (f : Frequency) : Polarization →ₗ[ℂ] Polarization :=
  (divergenceSymbol c f).smulRight
    (((laplacianSymbol c f : ℂ))⁻¹ • longitudinalVector c f)

theorem gradientProjection_apply (c : Momentum) (f : Frequency) (x : Polarization) :
    gradientProjection c f x =
      (divergenceSymbol c f x / (laplacianSymbol c f : ℂ)) • longitudinalVector c f := by
  simp [gradientProjection, smul_smul, div_eq_mul_inv]

theorem divergence_gradientProjection (c : Momentum) (f : Frequency)
    (hlap : laplacianSymbol c f ≠ 0) (x : Polarization) :
    divergenceSymbol c f (gradientProjection c f x) = divergenceSymbol c f x := by
  rw [gradientProjection_apply, map_smul, divergence_longitudinal, smul_eq_mul]
  exact div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr hlap)

theorem gradientProjection_idempotent (c : Momentum) (f : Frequency)
    (hlap : laplacianSymbol c f ≠ 0) (x : Polarization) :
    gradientProjection c f (gradientProjection c f x) = gradientProjection c f x := by
  rw [gradientProjection_apply c f (gradientProjection c f x),
    divergence_gradientProjection c f hlap, ← gradientProjection_apply]

theorem sub_gradientProjection_mem_transverse (c : Momentum) (f : Frequency)
    (hlap : laplacianSymbol c f ≠ 0) (x : Polarization) :
    x - gradientProjection c f x ∈ transversePolarization c f := by
  change divergenceSymbol c f (x - gradientProjection c f x) = 0
  rw [map_sub, divergence_gradientProjection c f hlap, sub_self]

def gradientProjectionMatrix (c : Momentum) (f : Frequency) : Matrix Direction Direction ℂ :=
  fun i j => conj (symbol c f i) * symbol c f j / (laplacianSymbol c f : ℂ)

theorem gradientProjectionMatrix_apply (c : Momentum) (f : Frequency) (x : Polarization) :
    (gradientProjectionMatrix c f).toEuclideanLin x = gradientProjection c f x := by
  apply WithLp.ofLp_injective 2
  funext i
  simp only [Matrix.ofLp_toLpLin, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
    gradientProjectionMatrix, gradientProjection_apply, WithLp.ofLp_smul,
    longitudinalVector, Pi.smul_apply, smul_eq_mul,
    divergenceSymbol, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_div,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

def longitudinalMatrix (c : Momentum) (f : Frequency) : Matrix Direction Direction ℂ :=
  fun i j => conj (symbol c f i) * symbol c f j

/-- The curl symbol has precisely the longitudinal null direction and
Laplacian strength on its transverse complement. -/
theorem curlSymbolMatrix_mul_adjoint (c : Momentum) (f : Frequency) :
    curlSymbolMatrix c f * (curlSymbolMatrix c f).conjTranspose =
      Matrix.diagonal (fun _ : Direction => (laplacianSymbol c f : ℂ)) -
        longitudinalMatrix c f := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [curlSymbolMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply,
      laplacianSymbol, longitudinalMatrix, Fin.sum_univ_three, Complex.ofReal_add, ← Complex.mul_conj] <;> ring

/-- On a transverse polarization, the curl-adjoint norm square is governed
by the scalar Laplacian symbol. -/
theorem curlSymbolMatrix_mul_adjoint_transverse (c : Momentum) (f : Frequency)
    (x : Polarization) (hx : x ∈ transversePolarization c f) :
    (curlSymbolMatrix c f * (curlSymbolMatrix c f).conjTranspose).toEuclideanLin x =
      (laplacianSymbol c f : ℂ) • x := by
  apply WithLp.ofLp_injective 2
  funext i
  rw [curlSymbolMatrix_mul_adjoint]
  change ((Matrix.diagonal (fun _ : Direction => (laplacianSymbol c f : ℂ)) -
    longitudinalMatrix c f) *ᵥ x.ofLp) i = _
  rw [Matrix.sub_mulVec, Pi.sub_apply, Matrix.mulVec_diagonal]
  have hx' : ∑ j, symbol c f j * x j = 0 := hx
  simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, longitudinalMatrix,
    mul_assoc, ← Finset.mul_sum, hx', mul_zero, sub_zero]

/-- The full transverse Fourier coordinate space. -/
abbrev TransverseCoordinates (c : Momentum) := PiLp 2 fun f => ↥(transversePolarization c f)

/-- Transverse low-frequency coordinates for the exact finite set selected
by the certificate. -/
abbrev LowTransverseCoordinates (c : Momentum) (low : Finset Frequency) :=
  PiLp 2 fun f : {f // f ∈ low} => transversePolarization c f

abbrev HighTransverseCoordinates (c : Momentum) (low : Finset Frequency) :=
  PiLp 2 fun f : {f // f ∉ low} => transversePolarization c f

theorem transverseCoordinates_finrank (c : Momentum)
    (hlap : ∀ f, laplacianSymbol c f ≠ 0) :
    Module.finrank ℂ (TransverseCoordinates c) = 4000 := by
  rw [(WithLp.linearEquiv 2 ℂ _).finrank_eq, Module.finrank_pi_fintype]
  simp [transversePolarization_finrank c _ (hlap _), Frequency, Cell]

theorem lowTransverseCoordinates_finrank (c : Momentum) (low : Finset Frequency)
    (hlap : ∀ f, laplacianSymbol c f ≠ 0) :
    Module.finrank ℂ (LowTransverseCoordinates c low) = 2 * low.card := by
  rw [(WithLp.linearEquiv 2 ℂ _).finrank_eq, Module.finrank_pi_fintype]
  simp [transversePolarization_finrank c _ (hlap _), mul_comm]

theorem highTransverseCoordinates_finrank (c : Momentum) (low : Finset Frequency)
    (hlap : ∀ f, laplacianSymbol c f ≠ 0) :
    Module.finrank ℂ (HighTransverseCoordinates c low) = 2 * (2000 - low.card) := by
  rw [(WithLp.linearEquiv 2 ℂ _).finrank_eq, Module.finrank_pi_fintype]
  simp [transversePolarization_finrank c _ (hlap _), Fintype.card_subtype_compl,
    Frequency, Cell, mul_comm]

abbrev FourierSpace := EuclideanSpace ℂ Electric

/-- The actual full Fourier-space transverse subspace. -/
def transverseSubspace (c : Momentum) : Submodule ℂ FourierSpace where
  carrier := {x | ∀ f, ∑ j, symbol c f j * x (j, f) = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy f
    simp only [PiLp.add_apply, mul_add, Finset.sum_add_distrib, hx f, hy f, add_zero]
  smul_mem' := by
    intro a x hx f
    simp only [PiLp.smul_apply, smul_eq_mul]
    calc
      _ = a * ∑ j, symbol c f j * x (j, f) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = 0 := by rw [hx f, mul_zero]

/-- Restricting frequency support preserves the transverse condition. -/
def supportedTransverseSubspace (c : Momentum) (support : Finset Frequency) :
    Submodule ℂ FourierSpace where
  carrier := {x | x ∈ transverseSubspace c ∧ ∀ f, f ∉ support → ∀ j, x (j, f) = 0}
  zero_mem' := ⟨(transverseSubspace c).zero_mem, by simp⟩
  add_mem' := by
    intro x y hx hy
    refine ⟨(transverseSubspace c).add_mem hx.1 hy.1, ?_⟩
    intro f hf j
    simp [hx.2 f hf j, hy.2 f hf j]
  smul_mem' := by
    intro a x hx
    refine ⟨(transverseSubspace c).smul_mem a hx.1, ?_⟩
    intro f hf j
    simp [hx.2 f hf j]

/-- A coordinate permutation identifies the actual transverse subspace with
its independent two-dimensional polarization fibers. -/
def transverseCoordinatesEquiv (c : Momentum) :
    TransverseCoordinates c ≃ₗ[ℂ] transverseSubspace c where
  toFun x := ⟨WithLp.toLp 2 (fun e => ((x e.2 : Polarization) e.1)), by
    intro f
    exact (x f).property⟩
  invFun x := WithLp.toLp 2 fun f =>
    ⟨WithLp.toLp 2 (fun j => (x : FourierSpace) (j, f)), x.property f⟩
  left_inv x := by rfl
  right_inv x := by rfl
  map_add' x y := by rfl
  map_smul' a x := by rfl

/-- The support-restricted version binds the finite low/high coordinate
dimensions directly to subspaces of the actual 6000-component Fourier field. -/
def supportedTransverseCoordinatesEquiv (c : Momentum) (support : Finset Frequency) :
    LowTransverseCoordinates c support ≃ₗ[ℂ] supportedTransverseSubspace c support where
  toFun x := ⟨WithLp.toLp 2 (fun e =>
    if h : e.2 ∈ support then ((x ⟨e.2, h⟩ : Polarization) e.1) else 0), by
      constructor
      · intro f
        by_cases hf : f ∈ support
        · have ht : ∑ j, symbol c f j * ((x ⟨f, hf⟩ : Polarization) j) = 0 :=
            (x ⟨f, hf⟩).property
          simpa only [dite_eq_left hf] using ht
        · simp [hf]
      · intro f hf j
        simp [hf]⟩
  invFun x := WithLp.toLp 2 fun f =>
    ⟨WithLp.toLp 2 (fun j => (x : FourierSpace) (j, f)), x.property.1 f⟩
  left_inv x := by
    apply WithLp.ofLp_injective 2
    funext f
    apply Subtype.ext
    apply WithLp.ofLp_injective 2
    funext j
    exact dite_eq_left f.property
  right_inv x := by
    apply Subtype.ext
    apply WithLp.ofLp_injective 2
    funext e
    change (if h : e.2 ∈ support then (x : FourierSpace) e else 0) = _
    split_ifs with h
    · rfl
    · exact (x.property.2 e.2 h e.1).symm
  map_add' x y := by
    apply Subtype.ext
    apply WithLp.ofLp_injective 2
    funext e
    change (if h : e.2 ∈ support then
      ((x ⟨e.2, h⟩ : Polarization) e.1 + (y ⟨e.2, h⟩ : Polarization) e.1) else 0) = _
    split_ifs <;> simp_all
  map_smul' a x := by
    apply Subtype.ext
    apply WithLp.ofLp_injective 2
    funext e
    change (if h : e.2 ∈ support then
      a * ((x ⟨e.2, h⟩ : Polarization) e.1) else 0) = _
    split_ifs <;> simp_all

theorem transverseSubspace_finrank (c : Momentum)
    (hlap : ∀ f, laplacianSymbol c f ≠ 0) :
    Module.finrank ℂ (transverseSubspace c) = 4000 := by
  rw [← (transverseCoordinatesEquiv c).finrank_eq]
  exact transverseCoordinates_finrank c hlap

theorem supportedTransverseSubspace_finrank (c : Momentum) (support : Finset Frequency)
    (hlap : ∀ f, laplacianSymbol c f ≠ 0) :
    Module.finrank ℂ (supportedTransverseSubspace c support) = 2 * support.card := by
  rw [← (supportedTransverseCoordinatesEquiv c support).finrank_eq]
  exact lowTransverseCoordinates_finrank c support hlap

/-- Coordinate restriction to a frequency set, in the actual Fourier field. -/
def frequencyRestriction (support : Finset Frequency) : FourierSpace →ₗ[ℂ] FourierSpace where
  toFun x := WithLp.toLp 2 fun e => if e.2 ∈ support then x e else 0
  map_add' x y := by
    apply WithLp.ofLp_injective 2
    funext e
    change (if e.2 ∈ support then x e + y e else 0) = _
    split_ifs <;> simp_all
  map_smul' a x := by
    apply WithLp.ofLp_injective 2
    funext e
    change (if e.2 ∈ support then a * x e else 0) = _
    split_ifs <;> simp_all

theorem frequencyRestriction_mem (c : Momentum) (support : Finset Frequency)
    (x : FourierSpace) (hx : x ∈ transverseSubspace c) :
    frequencyRestriction support x ∈ supportedTransverseSubspace c support := by
  constructor
  · intro f
    by_cases hf : f ∈ support
    · simpa only [frequencyRestriction, LinearMap.coe_mk, AddHom.coe_mk,
        PiLp.toLp_apply, ite_eq_left hf] using hx f
    · simp [frequencyRestriction, hf]
  · intro f hf j
    simp [frequencyRestriction, hf]

theorem frequencyRestriction_add_compl (support : Finset Frequency) (x : FourierSpace) :
    frequencyRestriction support x + frequencyRestriction supportᶜ x = x := by
  apply WithLp.ofLp_injective 2
  funext e
  by_cases he : e.2 ∈ support <;> simp [frequencyRestriction, he]

theorem supportedTransverse_sup_compl (c : Momentum) (support : Finset Frequency) :
    supportedTransverseSubspace c support ⊔ supportedTransverseSubspace c supportᶜ =
      transverseSubspace c := by
  apply le_antisymm
  · exact sup_le (fun _ h => h.1) (fun _ h => h.1)
  · intro x hx
    exact Submodule.mem_sup.mpr ⟨frequencyRestriction support x,
      frequencyRestriction_mem c support x hx, frequencyRestriction supportᶜ x,
      frequencyRestriction_mem c supportᶜ x hx, frequencyRestriction_add_compl support x⟩

theorem supportedTransverse_disjoint_compl (c : Momentum) (support : Finset Frequency) :
    Disjoint (supportedTransverseSubspace c support) (supportedTransverseSubspace c supportᶜ) := by
  rw [Submodule.disjoint_def]
  intro x hx hy
  apply WithLp.ofLp_injective 2
  funext e
  by_cases he : e.2 ∈ support
  · exact hy.2 e.2 (by simpa using he) e.1
  · exact hx.2 e.2 he e.1

theorem supportedTransverse_orthogonal_compl (c : Momentum) (support : Finset Frequency)
    (x y : FourierSpace) (hx : x ∈ supportedTransverseSubspace c support)
    (hy : y ∈ supportedTransverseSubspace c supportᶜ) : inner ℂ x y = 0 := by
  simp only [PiLp.inner_apply, RCLike.inner_apply]
  apply Finset.sum_eq_zero
  intro e _
  by_cases he : e.2 ∈ support
  · rw [hy.2 e.2 (by simpa using he) e.1, zero_mul]
  · rw [hx.2 e.2 he e.1, map_zero, mul_zero]

end Maxwell.Certificate.FourierBinding
