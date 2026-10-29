import Maxwell.Continuum.SelfAdjointResolventMaxwell
import Maxwell.Continuum.DetuningSpectrum

/-!
# Physical Maxwell detuning, inverse bounds, and residual recovery

The failure event uses the actual spectrum of the partial Maxwell operator.
The probability theorem takes an explicit finite cover of the spectrum in
the fixed counting window; proving that cover and its cardinality remains
a separate dependency. Every draw outside the event has a literal shifted
dielectric, a constructed inverse, and the stated conditioning guarantees.
-/

noncomputable section

namespace Maxwell.Continuum

open TopologicalSpace SelfAdjointResolvent

set_option backward.isDefEq.respectTransparency false

/-- The genuine spectral failure event for the actual nominal Maxwell operator. -/
def maxwellBadDraws (Ω : Opens Space) (ε : ScalarDielectric) (m N : ℕ) (τ : ℝ) :
    Finset ℕ :=
  Detuning.spectrumBadDraws (realSpectrum (maxwellOperator Ω ε)) τ
    (Detuning.radius m N τ) (Detuning.gridSize m N)

/-- A local spectral cover and its count control the actual continuum bad event. -/
theorem maxwell_detuning_probability (Ω : Opens Space) (ε : ScalarDielectric)
    (s : Finset ℝ) (m N : ℕ) (τ : ℝ)
    (hm : 0 < m) (hN : 0 < N) (hτ : 0 < τ) (hτupper : τ ≤ 1 / 64)
    (hcount : s.card ≤ N)
    (hlocal : ∀ eig ∈ realSpectrum (maxwellOperator Ω ε),
      eig ∈ Set.Icc (-(1 / 4 : ℝ)) (1 / 4) → eig ∈ s) :
    DetuningGrid.gridProbability (Detuning.gridSize m N)
      (Detuning.grid_pos m N _ hm hN (Detuning.gridSize_sufficient m N))
      (maxwellBadDraws Ω ε m N τ) ≤ 3 / (64 * (m : ℝ)) :=
  Detuning.spectrum_detuning_probability (realSpectrum (maxwellOperator Ω ε)) s
    m N _ τ hm hN hτ hτupper hcount (Detuning.gridSize_sufficient m N) hlocal

set_option maxHeartbeats 600000 in
/-- Every successful draw constructs a physical shifted material and the
actual Maxwell inverse with L², graph-norm and conditioning bounds. Its
source-residual bounds follow from `maxwell_inverse_residual` and
`maxwell_inverse_graph_residual`. -/
theorem sampled_maxwell_resolvent (Ω : Opens Space) (ε : ScalarDielectric)
    (m N j : ℕ) (τ : ℝ)
    (hm : 0 < m) (hN : 0 < N) (hτ : 0 < τ) (hτupper : τ ≤ 1 / 64)
    (hmargin : ∀ x, ε.coefficient x ≤ 24)
    (hj : j < Detuning.gridSize m N) (hgood : j ∉ maxwellBadDraws Ω ε m N τ) :
    ∃ εσ : ScalarDielectric,
      (∀ x, εσ.coefficient x = ε.coefficient x +
        DetuningGrid.midpoint τ (Detuning.gridSize m N) j) ∧
      ∃ R : BoundedInverse (maxwellOperator Ω εσ),
        ‖R.map‖ ≤ Detuning.inverseBudget m N τ ∧
        ‖maxwellGraphInverse Ω εσ R‖ ≤ 27 * Detuning.inverseBudget m N τ ∧
        ‖maxwellGraphMap Ω εσ‖ * ‖maxwellGraphInverse Ω εσ R‖ ≤
          702 * Detuning.inverseBudget m N τ := by
  let σ := DetuningGrid.midpoint τ (Detuning.gridSize m N) j
  have hsample := Detuning.sample_mem m N j τ hτ hj
  have hσ : 0 ≤ σ := hsample.1.le
  have hσupper : σ ≤ 1 := hsample.2.le.trans (hτupper.trans (by norm_num))
  have hupper := ε.shifted_upper_of_margin σ hmargin hσupper
  have hrad := Detuning.radius_pos m N τ hm hN hτ
  have hradupper : Detuning.radius m N τ ≤ 1 :=
    (Detuning.radius_le_tau m N τ hm hN hτ).trans (hτupper.trans (by norm_num))
  have hgap : ∀ eig ∈ realSpectrum (maxwellOperator Ω ε),
      Detuning.radius m N τ ≤ |σ - eig| := by
    intro eig heig
    rw [Detuning.radius_eq_inverseBudget_inv]
    have h := Detuning.gap_of_not_spectrumBadDraws
      (realSpectrum (maxwellOperator Ω ε)) m N _ j τ hj hgood eig heig
    exact h.trans_eq (abs_sub_comm eig σ)
  obtain ⟨R, hR, hgraph, hcondition⟩ := maxwell_spectral_gap_resolvent Ω ε σ hσ hupper
    hrad hradupper hgap
  have hinv : (Detuning.radius m N τ)⁻¹ = Detuning.inverseBudget m N τ := by
    rw [Detuning.radius_eq_inverseBudget_inv, one_div, inv_inv]
  have hR' := hR.trans_eq hinv
  have hgraph' := hgraph.trans_eq (congrArg (fun z : ℝ => 27 * z) hinv)
  have hcondition' := hcondition.trans_eq (congrArg (fun z : ℝ => 702 * z) hinv)
  exact ⟨ε.shifted σ hσ hupper, fun _ => rfl, R, hR', hgraph', hcondition'⟩

end Maxwell.Continuum
