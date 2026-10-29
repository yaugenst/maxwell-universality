import Maxwell.Continuum.AngularFourier
import Maxwell.Continuum.FreeFiber

/-! Exact norm-preserving unpacking of vector-valued physical L² into
the three-component Maxwell field space. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.VectorFieldL2

open MeasureTheory FreeFiber

abbrev L2 := Lp Polarization 2 (volume : Measure Space)

def coordinate (j : Fin 3) : L2 →L[ℂ] ScalarL2 :=
  (PiLp.proj 2 (fun _ : Fin 3 => ℂ) j).compLpL 2 volume

theorem coordinate_ae (j : Fin 3) (f : L2) :
    coordinate j f =ᵐ[volume] fun x => f x j :=
  ContinuousLinearMap.coeFn_compLpL _ f

def unpack : L2 →L[ℂ] FieldL2 :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 3 => ScalarL2)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi coordinate)

theorem unpack_coordinate (f : L2) (j : Fin 3) : unpack f j = coordinate j f := rfl

theorem unpack_ae (f : L2) (j : Fin 3) : unpack f j =ᵐ[volume] fun x => f x j :=
  coordinate_ae j f

theorem unpack_norm (f : L2) : ‖unpack f‖ = ‖f‖ := by
  have he : ‖unpack f‖^2 = ‖f‖^2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp only [unpack_coordinate, L2Dilation.norm_sq]
    rw [← integral_finsetSum Finset.univ (fun j _ =>
      (Lp.memLp (coordinate j f)).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0))]
    apply integral_congr_ae
    filter_upwards [ae_all_iff.mpr (fun j => coordinate_ae j f)] with x hx
    simp only [hx]
    exact (PiLp.norm_sq_eq_of_L2 _ (f x)).symm
  nlinarith [norm_nonneg (unpack f), norm_nonneg f]

def isometry : L2 →ₗᵢ[ℂ] FieldL2 where
  toLinearMap := unpack.toLinearMap
  norm_map' := unpack_norm

end Maxwell.Continuum.VectorFieldL2
