import Maxwell.Continuum.MomentumLeakageGeometry

/-! Exact physical Fourier support of the actual high-Bloch-momentum
projection, including all aliases. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.Auxiliary

open Bloch MeasureTheory

attribute [local irreducible] Bloch.unitary highMomentumProjection

theorem highMomentumProjection_fourier_ae (s : ℝ) (f : FieldL2) (k : Fin 3) :
    fieldFourier (highMomentumProjection s f) k =ᵐ[volume]
      fun ξ => if s ≤ quasiRadius ξ then fieldFourier f k ξ else 0 := by
  have hm : Measurable (fun ξ => if s ≤ quasiRadius ξ then fieldFourier f k ξ else (0 : ℂ)) :=
    (Lp.stronglyMeasurable (fieldFourier f k)).measurable.ite
      (measurableSet_le measurable_const quasiRadius_measurable) measurable_const
  apply (ae_join_iff (measurableSet_eq_fun
    (Lp.stronglyMeasurable (fieldFourier (highMomentumProjection s f) k)).measurable hm)).mpr
  filter_upwards [unitary_coordinate_ae (highMomentumProjection s f), unitary_coordinate_ae f,
    highMomentumProjection_ae s f] with q hp hf hP
  intro n
  rw [← hp n k, quasiRadius_join]
  by_cases hq : s ≤ ‖q.val‖
  · simp only [hq, ↓reduceIte] at hP ⊢
    rw [hP, hf n k]
  · simp only [hq, ↓reduceIte] at hP ⊢
    rw [hP]
    rfl

theorem lowMomentumProjection_fourier_ae (s : ℝ) (f : FieldL2) (k : Fin 3) :
    fieldFourier (f-highMomentumProjection s f) k =ᵐ[volume]
      fun ξ => if s ≤ quasiRadius ξ then 0 else fieldFourier f k ξ := by
  have he : fieldFourier (f-highMomentumProjection s f) k =
      fieldFourier f k-fieldFourier (highMomentumProjection s f) k := by
    rw [map_sub]
    rfl
  rw [he]
  filter_upwards [Lp.coeFn_sub (fieldFourier f k) (fieldFourier (highMomentumProjection s f) k),
    highMomentumProjection_fourier_ae s f k] with ξ hs hp
  rw [hs, Pi.sub_apply, hp]
  split_ifs <;> simp

#print axioms highMomentumProjection_fourier_ae
#print axioms lowMomentumProjection_fourier_ae

end Maxwell.Continuum.Auxiliary
