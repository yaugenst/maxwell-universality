import Maxwell.Green.PhysicalCompression

/-! Parseval for the actual finite lattice source and its Bloch polynomial.
The identity supplies the complete negative-band cost in the resolvent
Rayleigh estimate without a pointwise bound on the coherent profile. -/
namespace Maxwell.Defect

open MeasureTheory Maxwell.Spectral Maxwell.Spectral.Lattice Maxwell.Spectral.Bloch
open Maxwell.Green.PhysicalCompression
open scoped ENNReal

noncomputable section
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
variable {ι : Type*} [Fintype ι]

theorem scalarFiber_integrable_norm_sq (f : ScalarFiber) :
    Integrable (fun t : Torus => ‖f t‖ ^ 2) := by
  have h := (L2.integrable_inner (𝕜 := ℂ) f f).re
  simpa only [inner_self_eq_norm_sq_to_K, RCLike.re_ofReal_pow] using h

theorem scalarFiber_integral_norm_sq (f : ScalarFiber) :
    ∫ t : Torus, ‖f t‖ ^ 2 = ‖f‖ ^ 2 := by
  calc
    _ = (∫ t : Torus, inner ℂ (f t) (f t)).re := by
      simpa only [inner_self_eq_norm_sq_to_K, RCLike.re_ofReal_pow,
        RCLike.re_eq_complex_re] using
        (integral_re (L2.integrable_inner (𝕜 := ℂ) f f))
    _ = (inner ℂ f f).re := rfl
    _ = _ := by
      rw [← RCLike.re_eq_complex_re, inner_self_eq_norm_sq_to_K, RCLike.re_ofReal_pow]

theorem profile_component_integrable_norm_sq (edges : ι → Edge) (a : ι → ℂ)
    (r : Edge20) : Integrable (fun t : Torus => ‖profile edges a t r‖ ^ 2) := by
  refine (scalarFiber_integrable_norm_sq (transform (finiteField edges a) r)).congr ?_
  filter_upwards [transform_finiteField_ae edges a r] with t ht
  rw [ht]

theorem profile_integrable_norm_sq (edges : ι → Edge) (a : ι → ℂ) :
    Integrable (fun t : Torus => ∑ r, ‖profile edges a t r‖ ^ 2) :=
  integrable_finsetSum _ (fun r _ => profile_component_integrable_norm_sq edges a r)

/-- The exact Parseval identity for the finite physical source, including
all phases and repeated input edges. -/
theorem profile_parseval (edges : ι → Edge) (a : ι → ℂ) :
    ∫ t : Torus, ∑ r, ‖profile edges a t r‖ ^ 2 = ‖finiteField edges a‖ ^ 2 := by
  rw [integral_finsetSum _ (fun r _ => profile_component_integrable_norm_sq edges a r)]
  calc
    _ = ∑ r, ‖transform (finiteField edges a) r‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro r _
      rw [← scalarFiber_integral_norm_sq]
      apply integral_congr_ae
      filter_upwards [transform_finiteField_ae edges a r] with t ht
      rw [ht]
    _ = ‖transform (finiteField edges a)‖ ^ 2 := (PiLp.norm_sq_eq_of_L2 _ _).symm
    _ = _ := by rw [transform_norm]

theorem profile_vector_integrable_norm_sq (edges : ι → Edge) (a : ι → ℂ) :
    Integrable (fun t : Torus => ‖WithLp.toLp 2 (profile edges a t)‖ ^ 2) := by
  simpa only [PiLp.norm_sq_eq_of_L2, PiLp.toLp_apply] using profile_integrable_norm_sq edges a

theorem profile_vector_parseval (edges : ι → Edge) (a : ι → ℂ) :
    ∫ t : Torus, ‖WithLp.toLp 2 (profile edges a t)‖ ^ 2 = ‖finiteField edges a‖ ^ 2 := by
  simpa only [PiLp.norm_sq_eq_of_L2, PiLp.toLp_apply] using profile_parseval edges a

/-- The entire negative spectral contribution has the physical source norm
as its integral cost. -/
theorem profile_negative_cost (edges : ι → Edge) (a : ι → ℂ) (g : ℝ) :
    ∫ t : Torus, -(‖WithLp.toLp 2 (profile edges a t)‖ ^ 2 / g) =
      -(‖finiteField edges a‖ ^ 2 / g) := by
  rw [integral_neg, integral_div, profile_vector_parseval]

variable [DecidableEq ι]

theorem profile_embedding_parseval (edges : ι ↪ Edge) (a : EuclideanSpace ℂ ι) :
    ∫ t : Torus, ∑ r, ‖profile edges a t r‖ ^ 2 = ‖a‖ ^ 2 := by
  rw [profile_parseval, finiteField_extension, LinearIsometry.norm_map]

end
end Maxwell.Defect
