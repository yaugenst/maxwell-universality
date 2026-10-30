import Maxwell.Continuum.VacuumBoxInverse
import Maxwell.Continuum.BoxModesCutoffSpectrum
import Maxwell.Continuum.FourierConjugation
import Maxwell.Source

/-! The actual unit-cube continuum instance used for zero sources and the
smallest sparse inputs. Its decoder consumes no field samples. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace Maxwell.Continuum.VacuumBox

def source : testL2Closure domain := 0
def tolerance : ℚ := 1
def decode (S : Source.SparseSystem) (_w : Fin 0 → ℚ) : Fin S.n → ℚ := 0

theorem physical_volume : (MeasureTheory.volume (BoxModes.openBox lengths)).toReal = 1 := by
  rw [BoxModes.openBox_volume_toReal lengths (fun j => (lengths_pos j).le)]
  simp [lengths]

theorem tolerance_pos : 0 < tolerance := by norm_num [tolerance]

theorem source_real : fieldConjugation (source : FieldL2) = (source : FieldL2) := by
  exact map_zero _

theorem zero_admissible :
    ‖maxwellGraphMap domain material 0-source‖ ≤ (tolerance : ℝ)*‖source‖ := by
  simp [source,tolerance]

theorem zero_source_recovery (S : Source.SparseSystem) (eta : ℝ) (hb : S.source=0)
    (w : Fin 0 → ℚ) : Source.ResidualTarget S eta (decode S w) :=
  Source.zero_source_residual S eta hb

theorem smallest_input_recovery (p : Source.Parameters) (S : Source.SparseSystem)
    (hu : IsUnit (Source.realMatrix S)) (hm : S.nnz≤1)
    (eta : ℝ) (heta : Source.RequestedAccuracy p S eta) (w : Fin 0 → ℚ) :
    Source.ResidualTarget S eta (decode S w) := by
  by_cases hz : S.nnz=0
  · exact zero_source_recovery S eta (Source.source_zero_of_nnz_zero S hu hz) w
  · have hone : S.nnz=1 := by omega
    have heta1 : eta=1 := le_antisymm heta.2 (by simpa only [hone,Nat.cast_one,Real.one_rpow] using heta.1)
    have hx : Source.rationalVector (decode S w)=0 := by ext i; simp [decode,Source.rationalVector]
    simp [Source.ResidualTarget,hx,heta1]

theorem tolerance_polynomial (m : ℕ) (hm : 1≤m) (c : ℕ) :
    ((m : ℝ)^c)⁻¹ ≤ (tolerance : ℝ) := by
  have hpow : (1 : ℝ)≤(m : ℝ)^c := one_le_pow₀ (by exact_mod_cast hm)
  simpa only [tolerance,Rat.cast_one] using inv_le_one_of_one_le₀ hpow

/-- The physical inverse and exact no-sample decoder cover these branches
for every supplied field and every empty report, without a field-error premise. -/
theorem base_instance (p : Source.Parameters) (S : Source.SparseSystem)
    (hu : IsUnit (Source.realMatrix S)) (hbase : S.source=0 ∨ S.nnz≤1)
    (eta : ℝ) (heta : Source.RequestedAccuracy p S eta) :
    ‖inverse.map‖≤1 ∧
    ‖maxwellGraphInverse domain material inverse‖≤27 ∧
    ‖maxwellGraphMap domain material‖*‖maxwellGraphInverse domain material inverse‖≤702 ∧
    ∀ _u : OperatorDomain domain, ∀ w : Fin 0 → ℚ,
      Source.ResidualTarget S eta (decode S w) := by
  refine ⟨inverse_norm,inverse_graph_bounds.1,inverse_graph_bounds.2,?_⟩
  intro _u w
  rcases hbase with hb | hm
  · exact zero_source_recovery S eta hb w
  · exact smallest_input_recovery p S hu hm eta heta w

#print axioms physical_volume
#print axioms base_instance

end Maxwell.Continuum.VacuumBox
