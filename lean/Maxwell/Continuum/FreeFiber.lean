import Maxwell.Continuum.FreeFiberMultiplier
import Maxwell.Continuum.FreeFiberBlock
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Infinite continuum free Bloch fiber

The aliases are the actual integer lattice, each carrying three complex
polarizations. The momentum is `π/2 + q + πν`, appropriate to a period-two
medium at its antiperiodic corner. The inverse uses the full maximal domain
at the supplied complex momentum. A uniform block bound is explicit in its
contract; no analytic alias estimate or Bloch-transform theorem is asserted
here.
-/

noncomputable section

namespace Maxwell.Continuum.FreeFiber

abbrev Alias := Fin 3 → ℤ
abbrev FiberSpace := HilbertSum Alias Polarization

def aliasMomentum (q : Momentum) (ν : Alias) : Momentum :=
  fun j => (Real.pi : ℂ) / 2 + q j + (Real.pi : ℂ) * (ν j : ℂ)

/-- Maximal continuum fiber with total energy parameter `E`. -/
def operator (q : Momentum) (E : ℂ) : FiberSpace →ₗ.[ℂ] FiberSpace :=
  maximalOperator (fun ν => block (aliasMomentum q ν) E)

/-- The physical free background has dielectric constant seven. -/
def freeFiber (q : Momentum) : FiberSpace →ₗ.[ℂ] FiberSpace := operator q 7

theorem operator_domain_iff (q : Momentum) (E : ℂ) (u : FiberSpace) :
    u ∈ (operator q E).domain ↔
      Summable (fun ν => ‖block (aliasMomentum q ν) E (u ν)‖ ^ 2) := by
  change Memℓp (fun ν => block (aliasMomentum q ν) E (u ν)) 2 ↔ _
  rw [memℓp_gen_iff (by norm_num : 0 < (2 : ENNReal).toReal)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]

@[simp]
theorem operator_apply (q : Momentum) (E : ℂ) (u : (operator q E).domain) (ν : Alias) :
    operator q E u ν = block (aliasMomentum q ν) E (u.val ν) := rfl

theorem operator_graph_iff (q : Momentum) (E : ℂ) (u v : FiberSpace) :
    (u, v) ∈ (operator q E).graph ↔
      ∀ ν, block (aliasMomentum q ν) E (u ν) = v ν :=
  maximalOperator_graph_iff _ u v

/-- Closedness of the actual infinite fiber at every complex momentum. -/
theorem operator_isClosed (q : Momentum) (E : ℂ) : (operator q E).IsClosed :=
  maximalOperator_isClosed _

theorem freeFiber_isClosed (q : Momentum) : (freeFiber q).IsClosed := operator_isClosed q 7

/-- The inverse assembled from the explicit three-dimensional block formula. -/
def boundedInverse (q : Momentum) (E : ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ ν, ‖inverseBlock (aliasMomentum q ν) E‖ ≤ C) :
    FiberSpace →L[ℂ] FiberSpace :=
  boundedBlocks (fun ν => inverseBlock (aliasMomentum q ν) E) hC hbound

@[simp]
theorem boundedInverse_apply (q : Momentum) (E : ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ ν, ‖inverseBlock (aliasMomentum q ν) E‖ ≤ C)
    (u : FiberSpace) (ν : Alias) :
    boundedInverse q E hC hbound u ν = inverseBlock (aliasMomentum q ν) E (u ν) := rfl

theorem boundedInverse_norm_le (q : Momentum) (E : ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ ν, ‖inverseBlock (aliasMomentum q ν) E‖ ≤ C) :
    ‖boundedInverse q E hC hbound‖ ≤ C := boundedBlocks_norm_le _ hC hbound

/-- The explicit complex inverse lands in the full maximal domain at this `q`. -/
theorem boundedInverse_mem_domain (q : Momentum) (E : ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ ν, ‖inverseBlock (aliasMomentum q ν) E‖ ≤ C) (hE : E ≠ 0)
    (hp : ∀ ν, momentumSquare (aliasMomentum q ν) - E ≠ 0) (u : FiberSpace) :
    boundedInverse q E hC hbound u ∈ (operator q E).domain :=
  boundedBlocks_mem_maximalDomain _ _ hC hbound
    (fun ν => block_inverseBlock _ E hE (hp ν)) u

theorem operator_boundedInverse (q : Momentum) (E : ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ ν, ‖inverseBlock (aliasMomentum q ν) E‖ ≤ C) (hE : E ≠ 0)
    (hp : ∀ ν, momentumSquare (aliasMomentum q ν) - E ≠ 0) (u : FiberSpace) :
    operator q E ⟨boundedInverse q E hC hbound u,
      boundedInverse_mem_domain q E hC hbound hE hp u⟩ = u :=
  maximalOperator_boundedBlocks _ _ hC hbound
    (fun ν => block_inverseBlock _ E hE (hp ν)) u

theorem boundedInverse_operator (q : Momentum) (E : ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ ν, ‖inverseBlock (aliasMomentum q ν) E‖ ≤ C) (hE : E ≠ 0)
    (hp : ∀ ν, momentumSquare (aliasMomentum q ν) - E ≠ 0)
    (u : (operator q E).domain) :
    boundedInverse q E hC hbound (operator q E u) = u.val :=
  boundedBlocks_maximalOperator _ _ hC hbound
    (fun ν => inverseBlock_block _ E hE (hp ν)) u

end Maxwell.Continuum.FreeFiber
