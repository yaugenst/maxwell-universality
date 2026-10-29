import Maxwell.Green.Upper
import Mathlib.Analysis.Convex.Strict
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.LagrangeMultipliers
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

/-! Existence, uniqueness, and rate comparison for the supporting imaginary
point. Compactness, strict convexity, and Taylor comparison are ordinary
local spectral hypotheses; the support point and support rate are derived.
-/

noncomputable section

namespace Maxwell.Green

open Set Filter Real
open scoped Topology InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A nonzero linear functional cannot attain a maximum in the interior. -/
theorem support_not_mem_interior {s : Set E} {v β : E} (hv : v ≠ 0)
    (hmax : IsMaxOn (fun x => ⟪v, x⟫_ℝ) s β) : β ∉ interior s := by
  intro hβ
  have hl := hmax.isLocalMax (mem_interior_iff_mem_nhds.mp hβ)
  have hz : innerSL ℝ v = 0 :=
    hl.hasFDerivAt_eq_zero (innerSL ℝ v).hasFDerivAt
  have hn := congrArg norm hz
  have hnorm : ‖v‖ = 0 := by simpa only [innerSL_apply_norm, norm_zero] using hn
  exact hv (norm_eq_zero.mp hnorm)

/-- A support point of a continuous sublevel set lies on its level surface. -/
theorem support_on_level {F : E → ℝ} (hF : Continuous F)
    {ε : ℝ} {v β : E} (hv : v ≠ 0) (hβ : F β ≤ ε)
    (hmax : IsMaxOn (fun x => ⟪v, x⟫_ℝ) {x | F x ≤ ε} β) : F β = ε := by
  by_contra hne
  have hlt : F β < ε := lt_of_le_of_ne hβ hne
  have hopen : IsOpen {x | F x < ε} := isOpen_Iio.preimage hF
  have hnb : {x | F x ≤ ε} ∈ 𝓝 β :=
    Filter.mem_of_superset (hopen.mem_nhds hlt) (fun x (hx : F x < ε) => hx.le)
  exact support_not_mem_interior hv hmax (mem_interior_iff_mem_nhds.mpr hnb)

/-- Strict convexity rules out two distinct support points. -/
theorem support_unique {s : Set E} (hstrict : StrictConvex ℝ s)
    {v β γ : E} (hv : v ≠ 0) (hβ : β ∈ s) (hγ : γ ∈ s)
    (hmaxβ : IsMaxOn (fun x => ⟪v, x⟫_ℝ) s β)
    (hmaxγ : IsMaxOn (fun x => ⟪v, x⟫_ℝ) s γ) : β = γ := by
  by_contra hne
  let z : E := (1 / 2 : ℝ) • β + (1 / 2 : ℝ) • γ
  have hz : z ∈ interior s := hstrict hβ hγ hne (by norm_num) (by norm_num) (by norm_num)
  have heq : ⟪v, γ⟫_ℝ = ⟪v, β⟫_ℝ := le_antisymm (hmaxβ hγ) (hmaxγ hβ)
  have hzval : ⟪v, z⟫_ℝ = ⟪v, β⟫_ℝ := by
    dsimp [z]
    rw [inner_add_right, inner_smul_right, inner_smul_right, heq]
    ring
  have hmaxz : IsMaxOn (fun x => ⟪v, x⟫_ℝ) s z := by
    intro x hx
    change ⟪v, x⟫_ℝ ≤ ⟪v, z⟫_ℝ
    rw [hzval]
    exact hmaxβ hx
  exact support_not_mem_interior hv hmaxz hz

/-- The supporting imaginary point exists, lies on the energy level, and is
unique. This is an extreme-value conclusion, not an existence premise. -/
theorem exists_unique_support_point {F : E → ℝ} (hF : Continuous F)
    (ε : ℝ) (hcompact : IsCompact {x | F x ≤ ε}) (hzero : F 0 < ε)
    (hstrict : StrictConvex ℝ {x | F x ≤ ε}) (v : E) (hv : v ≠ 0) :
    ∃! β : E, F β = ε ∧ IsMaxOn (fun x => ⟪v, x⟫_ℝ) {x | F x ≤ ε} β := by
  obtain ⟨β, hβ, hmax⟩ := hcompact.exists_isMaxOn ⟨0, hzero.le⟩
    (innerSL ℝ v).continuous.continuousOn
  refine ⟨β, ⟨support_on_level hF hv hβ hmax, hmax⟩, ?_⟩
  intro γ hγ
  exact support_unique hstrict hv hγ.1.le hβ hγ.2 hmax

/-- An interior origin makes every nonzero directional support value positive. -/
theorem support_pairing_pos {s : Set E} (hzero : (0 : E) ∈ interior s)
    {v β : E} (hv : v ≠ 0)
    (hmax : IsMaxOn (fun x => ⟪v, x⟫_ℝ) s β) : 0 < ⟪v, β⟫_ℝ := by
  by_contra hnot
  have hle : ⟪v, β⟫_ℝ ≤ 0 := le_of_not_gt hnot
  have hmaxzero : IsMaxOn (fun x => ⟪v, x⟫_ℝ) s (0 : E) := by
    intro x hx
    change ⟪v, x⟫_ℝ ≤ ⟪v, 0⟫_ℝ
    simpa only [inner_zero_right] using (hmax hx).trans hle
  exact support_not_mem_interior hv hmaxzero hzero

/-- The normal at a regular smooth support point is a positive multiple of
the supporting direction. Lagrange multipliers give proportionality, and
the inward segment to the interior origin fixes its sign. -/
theorem support_gradient_positive_multiple [CompleteSpace E]
    {F : E → ℝ} (hF : Continuous F) {ε : ℝ}
    (hconv : Convex ℝ {x | F x ≤ ε}) (hzero : F 0 < ε)
    {v β g : E} (hv : v ≠ 0) (hlevel : F β = ε)
    (hmax : IsMaxOn (fun x => ⟪v, x⟫_ℝ) {x | F x ≤ ε} β)
    (hderiv : HasStrictFDerivAt F (innerSL ℝ g) β) (hgzero : g ≠ 0) :
    ∃ χ : ℝ, 0 < χ ∧ g = χ • v := by
  have hmaxlevel : IsMaxOn (fun x => ⟪v, x⟫_ℝ) {x | F x = F β} β := by
    intro x hx
    apply hmax
    change F x ≤ ε
    exact (hx.trans hlevel).le
  have hextr : IsLocalExtrOn (fun x => ⟪v, x⟫_ℝ) {x | F x = F β} β :=
    Or.inr hmaxlevel.isLocalMaxOn
  obtain ⟨a, b, hab, hlin⟩ :=
    hextr.exists_multipliers_of_hasStrictFDerivAt_1d hderiv
      (innerSL ℝ v).hasStrictFDerivAt
  have hpoint (x : E) : a * ⟪g, x⟫_ℝ + b * ⟪v, x⟫_ℝ = 0 := by
    have h := congrArg (fun L : E →L[ℝ] ℝ => L x) hlin
    exact h
  have ha : a ≠ 0 := by
    intro ha
    have hp := hpoint v
    rw [ha, zero_mul, zero_add, real_inner_self_eq_norm_sq] at hp
    have hb : b = 0 := (mul_eq_zero.mp hp).resolve_right
      (pow_ne_zero 2 (norm_ne_zero_iff.mpr hv))
    exact hab (by simp [ha, hb])
  have hg : g = (-b / a) • v := by
    apply ext_inner_right ℝ
    intro x
    rw [real_inner_smul_left, div_mul_eq_mul_div]
    apply (eq_div_iff ha).mpr
    nlinarith [hpoint x]
  have hopen : IsOpen {x | F x < ε} := isOpen_Iio.preimage hF
  have hzeroInterior : (0 : E) ∈ interior {x | F x ≤ ε} :=
    mem_interior_iff_mem_nhds.mpr
      (Filter.mem_of_superset (hopen.mem_nhds hzero) (fun x (hx : F x < ε) => hx.le))
  have hrate := support_pairing_pos hzeroInterior hv hmax
  have hFmax : IsMaxOn F {x | F x ≤ ε} β := by
    intro x hx
    change F x ≤ F β
    rw [hlevel]
    exact hx
  have hsegment : segment ℝ β (0 : E) ⊆ {x | F x ≤ ε} :=
    hconv.segment_subset hlevel.le hzero.le
  have htangent := sub_mem_posTangentConeAt_of_segment_subset hsegment
  have hnormal := hFmax.isLocalMaxOn.hasFDerivWithinAt_nonpos
    hderiv.hasFDerivAt.hasFDerivWithinAt htangent
  simp only [zero_sub, innerSL_apply_apply, inner_neg_right] at hnormal
  have hχnonneg : 0 ≤ -b / a := by
    rw [hg, real_inner_smul_left] at hnormal
    nlinarith
  have hχne : -b / a ≠ 0 := by
    intro hzeroχ
    exact hgzero (by simpa only [hzeroχ, zero_smul] using hg)
  exact ⟨-b / a, lt_of_le_of_ne hχnonneg hχne.symm, hg⟩

/-- The compact strictly convex smooth level has a unique regular support
point satisfying the positive normal equation. -/
theorem exists_unique_regular_support_point [CompleteSpace E]
    {F : E → ℝ} (hF : Continuous F) (g : E → E)
    (ε : ℝ) (hcompact : IsCompact {x | F x ≤ ε}) (hzero : F 0 < ε)
    (hstrict : StrictConvex ℝ {x | F x ≤ ε})
    (hderiv : ∀ x, F x = ε → HasStrictFDerivAt F (innerSL ℝ (g x)) x)
    (hregular : ∀ x, F x = ε → g x ≠ 0)
    (v : E) (hv : v ≠ 0) :
    ∃! β : E, F β = ε ∧ IsMaxOn (fun x => ⟪v, x⟫_ℝ) {x | F x ≤ ε} β ∧
      ∃ χ : ℝ, 0 < χ ∧ g β = χ • v := by
  obtain ⟨β, hβ, huniq⟩ := exists_unique_support_point hF ε hcompact hzero hstrict v hv
  refine ⟨β, ⟨hβ.1, hβ.2, support_gradient_positive_multiple hF hstrict.convex hzero
    hv hβ.1 hβ.2 (hderiv β hβ.1) (hregular β hβ.1)⟩, ?_⟩
  intro γ hγ
  exact huniq γ ⟨hγ.1, hγ.2.1⟩

/-- The exact support rate is bracketed by enclosing ellipsoid support
rates. The inner ellipsoid supplies a concrete competitor. -/
theorem support_rate_bounds_of_ellipsoids
    (P Q : E →L[ℝ] E) (hPQ : ∀ x, P (Q x) = x) (hQP : ∀ x, Q (P x) = x)
    (hsym : ∀ x y, ⟪P x, y⟫_ℝ = ⟪x, P y⟫_ℝ)
    {s : Set E} {v β : E} (hβ : β ∈ s)
    (hmax : IsMaxOn (fun x => ⟪v, x⟫_ℝ) s β)
    (rInner rOuter : ℝ) (hrInner : 0 ≤ rInner)
    (hinner : ∀ x, ‖Q x‖ ≤ rInner → x ∈ s)
    (houter : ∀ x ∈ s, ‖Q x‖ ≤ rOuter) :
    rInner * ‖P v‖ ≤ ⟪v, β⟫_ℝ ∧ ⟪v, β⟫_ℝ ≤ rOuter * ‖P v‖ := by
  constructor
  · have hadm := ellipsoidSupportPoint_admissible P Q hQP rInner hrInner v
    have h := hmax (hinner _ hadm)
    change ⟪v, ellipsoidSupportPoint P rInner v⟫_ℝ ≤ ⟪v, β⟫_ℝ at h
    rw [real_inner_comm (ellipsoidSupportPoint P rInner v) v,
      ellipsoidSupportPoint_pairing P hsym] at h
    exact h
  · rw [real_inner_comm β v]
    exact ellipsoid_pairing_le P Q hPQ hsym rOuter β v (houter β hβ)

/-- The two quadratic Taylor comparisons give explicit enclosing radii.
Only local comparisons are required: the lower bound on the sublevel and
the upper bound on the candidate inner ellipsoid. Here `a` and `b` are the
lower and upper quadratic coefficients, commonly `a=1-δ`, `b=1+δ`. -/
theorem sublevel_between_ellipsoids
    (F : E → ℝ) (Q : E →L[ℝ] E) (ε a b : ℝ)
    (hε : 0 ≤ ε) (ha : 0 < a) (hb : 0 < b)
    (hlower : ∀ x, F x ≤ ε → a * ‖Q x‖ ^ 2 / 2 ≤ F x)
    (hupper : ∀ x, ‖Q x‖ ≤ sqrt (2 * ε / b) → F x ≤ b * ‖Q x‖ ^ 2 / 2) :
    (∀ x, ‖Q x‖ ≤ sqrt (2 * ε / b) → F x ≤ ε) ∧
      (∀ x, F x ≤ ε → ‖Q x‖ ≤ sqrt (2 * ε / a)) := by
  have hsqb : sqrt (2 * ε / b) ^ 2 = 2 * ε / b :=
    sq_sqrt (by positivity)
  have hsqa : sqrt (2 * ε / a) ^ 2 = 2 * ε / a :=
    sq_sqrt (by positivity)
  constructor
  · intro x hx
    have hs : ‖Q x‖ ^ 2 ≤ 2 * ε / b := by
      nlinarith [norm_nonneg (Q x), sqrt_nonneg (2 * ε / b)]
    have hmul := (le_div_iff₀ hb).mp hs
    exact (hupper x hx).trans (by nlinarith)
  · intro x hx
    have hs : ‖Q x‖ ^ 2 ≤ 2 * ε / a := by
      apply (le_div_iff₀ ha).mpr
      nlinarith [hlower x hx]
    nlinarith [norm_nonneg (Q x), sqrt_nonneg (2 * ε / a)]

/-- Quadratic Taylor control yields the support-rate comparison appearing
in the Green exponent, with no assumed asymptotic for the maximizing point. -/
theorem support_rate_bounds_of_quadratic_comparison
    (F : E → ℝ) (P Q : E →L[ℝ] E)
    (hPQ : ∀ x, P (Q x) = x) (hQP : ∀ x, Q (P x) = x)
    (hsym : ∀ x y, ⟪P x, y⟫_ℝ = ⟪x, P y⟫_ℝ)
    (ε a b : ℝ) (hε : 0 ≤ ε) (ha : 0 < a) (hb : 0 < b)
    (hlower : ∀ x, F x ≤ ε → a * ‖Q x‖ ^ 2 / 2 ≤ F x)
    (hupper : ∀ x, ‖Q x‖ ≤ sqrt (2 * ε / b) → F x ≤ b * ‖Q x‖ ^ 2 / 2)
    (v β : E) (hβ : F β ≤ ε)
    (hmax : IsMaxOn (fun x => ⟪v, x⟫_ℝ) {x | F x ≤ ε} β) :
    sqrt (2 * ε / b) * ‖P v‖ ≤ ⟪v, β⟫_ℝ ∧
      ⟪v, β⟫_ℝ ≤ sqrt (2 * ε / a) * ‖P v‖ := by
  obtain ⟨hi, ho⟩ := sublevel_between_ellipsoids F Q ε a b hε ha hb hlower hupper
  exact support_rate_bounds_of_ellipsoids P Q hPQ hQP hsym hβ hmax
    _ _ (sqrt_nonneg _) hi ho

end Maxwell.Green
