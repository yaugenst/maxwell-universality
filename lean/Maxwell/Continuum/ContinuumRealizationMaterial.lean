import Maxwell.Continuum.ContinuumRealizationTuning
import Maxwell.Continuum.ContinuumRealizationEnergy
import Maxwell.Continuum.ProfileDielectric

/-! The literal encoded dielectric, its random dyadic detuning, and the
actual PEC inverse for every good draw. Calibration inputs here are only
finite rational enclosures of the specified continuum quantities. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

namespace Maxwell.Continuum.RealizationParameters

open MasterConstants Maxwell.Composition Auxiliary EffectiveMass FiniteAuxiliary
open SelfAdjointResolvent
attribute [local irreducible] Cs exponent Ls Parameters.sourceInput muH realMode

variable (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0 < S.nnz)

/-- Finite calibration results and their proved containment/width semantics.
No operator or analytic estimate is a field of this interface. -/
structure Enclosures where
  mode : Calibration.RationalInterval
  coupling : Fin 3 → Calibration.RationalInterval
  mode_contains : mode.Contains
    (muH (energyCalibration p S hm) (inverse_length_le_1024 (length_master p S hm)))
  mode_width : mode.width ≤ (zeta p S hm)^2/8
  coupling_contains : ∀ j, (coupling j).Contains
    (usefulCoupling (length_master p S hm) (energyCalibration p S hm) (spacing p S hm) j)
  coupling_width : ∀ j, (coupling j).width ≤ (zeta p S hm)^2/16

namespace Enclosures

variable {p S hm}
variable (C : Enclosures p S hm) (hb : S.source ≠ 0)

abbrev wellStrength : SourceDecoration.Vertex S (precision p S hm) → ℚ :=
  strength p S hm C.mode C.coupling

include hb in
theorem wellStrength_spec (i : SourceDecoration.Vertex S (precision p S hm)) :
    0 < C.wellStrength i ∧
    (C.wellStrength i : ℝ) ≤ (2 : ℝ)^130*(length p S hm : ℝ)⁻¹^2 ∧
    |(C.wellStrength i : ℝ)⁻¹-
      (muH (energyCalibration p S hm) (inverse_length_le_1024 (length_master p S hm))+
        (targetDiagonal p S hm C.coupling i : ℝ))| ≤ (zeta p S hm : ℝ)^2 :=
  strength_bounds p S hm (energyCalibration p S hm) hb C.mode C.coupling
    C.mode_contains C.mode_width C.coupling_contains C.coupling_width i

include hb in
theorem wellStrength_nonneg (i : SourceDecoration.Vertex S (precision p S hm)) :
    (0 : ℝ) ≤ C.wellStrength i := by exact_mod_cast (C.wellStrength_spec hb i).1.le

include hb in
theorem wellStrength_le_one (i : SourceDecoration.Vertex S (precision p S hm)) :
    (C.wellStrength i : ℝ) ≤ 1 :=
  (C.wellStrength_spec hb i).2.1 |>.trans (strength_budget_le_one p S hm)

theorem well_disjoint : Pairwise fun i j =>
    Disjoint (Metric.ball (centers p S hm i) ((length p S hm : ℝ)⁻¹)⁻¹)
      (Metric.ball (centers p S hm j) ((length p S hm : ℝ)⁻¹)⁻¹) := by
  simpa only [inv_inv] using centers_disjoint p S hm

def baseDielectric (N : ℕ) : ScalarDielectric :=
  Profile.encodedDielectric N (inverse_length_pos (length_master p S hm))
    (centers p S hm) (fun i => (C.wellStrength i : ℝ))
    (C.wellStrength_nonneg hb) (C.wellStrength_le_one hb) (well_disjoint (p := p) (S := S) (hm := hm))
    (energy p S hm) (energy_abs p S hm)

theorem baseDielectric_margin (N : ℕ) (x : Space) : (C.baseDielectric hb N).coefficient x ≤ 24 :=
  Profile.encodedDielectric_margin N (inverse_length_pos (length_master p S hm))
    (centers p S hm) (fun i => (C.wellStrength i : ℝ))
    (C.wellStrength_nonneg hb) (C.wellStrength_le_one hb) (well_disjoint (p := p) (S := S) (hm := hm))
    (energy p S hm) (energy_abs p S hm) x

end Enclosures

abbrev drawCount : ℕ := Detuning.gridSize S.nnz (count p S hm)
abbrev sample (j : ℕ) : ℝ := DetuningGrid.midpoint (radius p S hm) (drawCount p S hm) j

theorem sample_bounds (j : Fin (drawCount p S hm)) :
    0 ≤ sample p S hm j ∧ sample p S hm j ≤ (length p S hm : ℝ)⁻¹^4/64 ∧
    16*sample p S hm j*(length p S hm : ℝ)^4 ≤ (zeta p S hm : ℝ)^2/2^20 := by
  have hj := DetuningGrid.midpoint_mem (radius p S hm) (drawCount p S hm) j
    (radius_pos p S hm) j.isLt
  exact ⟨hj.1.le, detuning_bounds p S hm hj.2.le⟩

theorem sample_le_one (j : Fin (drawCount p S hm)) : sample p S hm j ≤ 1 := by
  have hj := DetuningGrid.midpoint_mem (radius p S hm) (drawCount p S hm) j
    (radius_pos p S hm) j.isLt
  exact hj.2.le.trans ((radius_upper p S hm).trans (by norm_num))

namespace Enclosures

variable {p S hm}
variable (C : Enclosures p S hm) (hb : S.source ≠ 0) (N : ℕ)

def outputDielectric (j : Fin (drawCount p S hm)) : ScalarDielectric :=
  (C.baseDielectric hb N).shifted (sample p S hm j) (sample_bounds p S hm j).1
    ((C.baseDielectric hb N).shifted_upper_of_margin (sample p S hm j)
      (C.baseDielectric_margin hb N) (sample_le_one p S hm j))

theorem outputDielectric_coefficient (j : Fin (drawCount p S hm)) (x : Space) :
    (C.outputDielectric hb N j).coefficient x =
      PeriodicMaterial.coefficient x+(energy p S hm : ℝ)+sample p S hm j+
        Profile.encodedWellCoefficient N (length p S hm : ℝ)⁻¹ (centers p S hm)
          (fun i => (C.wellStrength i : ℝ)) x := by
  change (PeriodicMaterial.coefficient x+(energy p S hm : ℝ)+
    Profile.encodedWellCoefficient N (length p S hm : ℝ)⁻¹ (centers p S hm)
      (fun i => (C.wellStrength i : ℝ)) x)+sample p S hm j = _
  ring

def materialError (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0 < S.nnz) (M : ℕ) : ℝ :=
  3*((2 : ℝ)^130*(length p S hm : ℝ)⁻¹^2)*(1/2 : ℝ)^(M+24)

theorem outputDielectric_multiplier_error (j : Fin (drawCount p S hm)) :
    ‖(C.outputDielectric hb N j).multiplier-
      assembledMaterial (length p S hm : ℝ)⁻¹ ((energy p S hm : ℝ)+sample p S hm j)
        (centers p S hm) (fun i => (C.wellStrength i : ℝ))‖ ≤ materialError p S hm N := by
  let η := Profile.idealDielectric (inverse_length_pos (length_master p S hm))
    (centers p S hm) (fun i => (C.wellStrength i : ℝ))
    (C.wellStrength_nonneg hb) (C.wellStrength_le_one hb) (well_disjoint (p := p) (S := S) (hm := hm))
    (energy p S hm) (energy_abs p S hm)
  have he : (C.outputDielectric hb N j).multiplier-
      assembledMaterial (length p S hm : ℝ)⁻¹ ((energy p S hm : ℝ)+sample p S hm j)
        (centers p S hm) (fun i => (C.wellStrength i : ℝ)) =
      (C.baseDielectric hb N).multiplier-η.multiplier := by
    rw [outputDielectric, ScalarDielectric.shifted_multiplier]
    rw [show η.multiplier = PeriodicMaterial.dielectric.multiplier+
      ((energy p S hm : ℝ) : ℂ) • ContinuousLinearMap.id ℂ FieldL2+
        finiteWellOperator (length p S hm : ℝ)⁻¹ (centers p S hm)
          (fun i => (C.wellStrength i : ℝ)) from
      Profile.idealDielectric_multiplier _ _ _ _ _ _ _ _]
    simp only [assembledMaterial, Complex.ofReal_add]
    module
  rw [he]
  exact Profile.encodedDielectric_multiplier_error N
    (inverse_length_pos (length_master p S hm)) (centers p S hm)
    (fun i => (C.wellStrength i : ℝ)) (C.wellStrength_nonneg hb)
    (C.wellStrength_le_one hb) (well_disjoint (p := p) (S := S) (hm := hm)) (energy p S hm) (energy_abs p S hm)
    (by positivity) (fun i => (C.wellStrength_spec hb i).2.1)

def badDraws : Finset ℕ := maxwellBadDraws (BoxModes.boxDomain (BoxCutoff.side (box p S hm)))
  (C.baseDielectric hb N) S.nnz (count p S hm) (radius p S hm)

private theorem coefficient_ext {ε η : ScalarDielectric}
    (h : ∀ x, ε.coefficient x = η.coefficient x) : ε = η := by
  cases ε
  cases η
  have he := funext h
  cases he
  rfl

theorem good_draw_inverse (j : Fin (drawCount p S hm)) (hgood : j.val ∉ C.badDraws hb N) :
    ∃ R : BoundedInverse (maxwellOperator (BoxModes.boxDomain (BoxCutoff.side (box p S hm)))
        (C.outputDielectric hb N j)),
      ‖R.map‖ ≤ (inverseBound p S hm : ℝ) ∧
      ‖maxwellGraphInverse (BoxModes.boxDomain (BoxCutoff.side (box p S hm)))
        (C.outputDielectric hb N j) R‖ ≤ 27*(inverseBound p S hm : ℝ) ∧
      ‖maxwellGraphMap (BoxModes.boxDomain (BoxCutoff.side (box p S hm)))
          (C.outputDielectric hb N j)‖*
        ‖maxwellGraphInverse (BoxModes.boxDomain (BoxCutoff.side (box p S hm)))
          (C.outputDielectric hb N j) R‖ ≤ 702*(inverseBound p S hm : ℝ) := by
  rw [box_sides p S hm]
  have hgood' : j.val ∉ maxwellBadDraws
      (BoxModes.boxDomain (fun k => (Parameters.sourcePhysicalLengths p S hm k : ℝ)))
      (C.baseDielectric hb N) S.nnz (count p S hm) (radius p S hm) := by
    simpa only [badDraws, box_sides] using hgood
  obtain ⟨εσ, hεσ, R, hR, hg, hc⟩ := (C.baseDielectric hb N).box_sampled_resolvent
    (Parameters.sourcePhysicalLengths p S hm)
    S.nnz j (radius p S hm) hm (radius_pos p S hm) (radius_upper p S hm)
    (C.baseDielectric_margin hb N) j.isLt hgood'
  have he : εσ = C.outputDielectric hb N j := coefficient_ext hεσ
  subst εσ
  exact ⟨R, by simpa only [inverseBound_eq, count, Parameters.sourceSpectralBudget] using hR,
    by simpa only [inverseBound_eq, count, Parameters.sourceSpectralBudget] using hg,
    by simpa only [inverseBound_eq, count, Parameters.sourceSpectralBudget] using hc⟩

theorem badDraws_probability :
    DetuningGrid.gridProbability (drawCount p S hm)
      (Detuning.grid_pos S.nnz (count p S hm) (drawCount p S hm) hm
        (Parameters.sourceSpectralBudget_pos p S hm) (Detuning.gridSize_sufficient _ _))
      (C.badDraws hb N) ≤ 3/(64*(S.nnz : ℝ)) := by
  simpa only [badDraws, box_sides, drawCount, count, Parameters.sourceSpectralBudget] using
    (C.baseDielectric hb N).box_detuning_probability (Parameters.sourcePhysicalLengths p S hm)
      (Parameters.sourcePhysicalLengths_pos p S hm) S.nnz (radius p S hm) hm
      (radius_pos p S hm) (radius_upper p S hm)

#print axioms outputDielectric_multiplier_error
#print axioms good_draw_inverse
#print axioms badDraws_probability

end Enclosures
end Maxwell.Continuum.RealizationParameters
