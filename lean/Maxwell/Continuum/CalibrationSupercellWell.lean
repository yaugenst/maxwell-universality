import Maxwell.Continuum.CalibrationSupercellMultiplier
import Maxwell.Continuum.CalibrationSupercellRoot
import Maxwell.Continuum.EffectiveMassWell

/-! Exact physical well multiplication under the full supercell embedding.
The statement covers every square-summable alias field. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048

namespace Maxwell.Continuum.Calibration.Supercell

open FreeFiber CellGauge CellBandFourier UnitAddTorus MeasureTheory Set EffectiveMass

variable (M : ℕ) [NeZero M]

theorem Qh_embedding_single (hEven : Even M) {L : ℝ} (hL : 1≤L)
    (hM : 16*(L+1)≤(M : ℝ)) (hs : 4≤2*(M : ℝ)/L)
    (n : Alias) (v : Polarization) :
    Qh L⁻¹ (embedding M (lp.single 2 n v))=
      physicalMultiplier M (rootTorus (2*(M : ℝ)/L) hs)
        (embedding M (lp.single 2 n v)) := by
  classical
  apply PiLp.ext
  intro i
  apply Lp.ext
  filter_upwards [Qh_ae L⁻¹ (embedding M (lp.single 2 n v)) i,
    physicalMultiplier_ae M (rootTorus (2*(M : ℝ)/L) hs)
      (embedding M (lp.single 2 n v)) i,
    embedding_single_ae M hEven n v i] with x hq hp he
  rw [hq,hp]
  by_cases hx : ∃a : Grid M, x∈spatialBox (representative M a)
  · obtain ⟨a,ha⟩ := hx
    rw [rootTorus_on_cell M hL hM hs a ha]
  · have hz : embedding M (lp.single 2 n v) i x=0 := by
      rw [he]
      have hz : (∑ a : Grid M, (spatialBox (representative M a)).indicator
          (fun x => mFourier n (torusPoint M x)*v i) x)=0 := by
        apply Finset.sum_eq_zero
        intro a _
        exact indicator_of_notMem (fun h => hx ⟨a,h⟩) _
      rw [hz,mul_zero]
    rw [hz,mul_zero,mul_zero]

theorem Qh_embedding (hEven : Even M) {L : ℝ} (hL : 1≤L)
    (hM : 16*(L+1)≤(M : ℝ)) (hs : 4≤2*(M : ℝ)/L) (u : FiberSpace) :
    Qh L⁻¹ (embedding M u)=
      embedding M (aliasMultiplier (rootTorus (2*(M : ℝ)/L) hs) u) := by
  rw [embedding_multiplier M hEven _ (rootTorus_coefficients_summable _ hs).of_norm]
  have he : (Qh L⁻¹).comp (embedding M).toContinuousLinearMap=
      (physicalMultiplier M (rootTorus (2*(M : ℝ)/L) hs)).comp
        (embedding M).toContinuousLinearMap := by
    apply lp.ext_continuousLinearMap (p := 2) (E := fun _ : Alias => Polarization)
      ENNReal.ofNat_ne_top
    intro n
    apply ContinuousLinearMap.ext
    intro v
    exact Qh_embedding_single M hEven hL hM hs n v
  exact congrArg (fun A : FiberSpace →L[ℂ] FieldL2 => A u) he

#print axioms Qh_embedding

end Maxwell.Continuum.Calibration.Supercell
