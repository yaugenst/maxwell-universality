import Maxwell.Continuum.ContinuumRealizationParameters
import Maxwell.Continuum.FiniteAuxiliaryGeometry
import Maxwell.Continuum.FiniteAuxiliarySourceAmplitudes
import Maxwell.Continuum.FiniteAuxiliarySourcePEC

/-! The selected source layout, logical inverse budget, and actual boundary
and interaction tails required by the continuum recovery theorem. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace Maxwell.Continuum.RealizationParameters

open MasterConstants Maxwell.Composition FiniteAuxiliary
attribute [local irreducible] Cs exponent Ls Parameters.sourceInput

variable (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0 < S.nnz)

abbrev sites : ℕ := Fintype.card (SourceDecoration.Vertex S (precision p S hm))
abbrev box : Fin 3 → ℕ := Parameters.sourceBox p S hm (stage p S hm)
abbrev shift : Bloch.Alias := sourceCommonShift p S hm (stage p S hm)
abbrev centers : SourceDecoration.Vertex S (precision p S hm) → Space :=
  shiftedRoutedCenters S (precision p S hm) (length p S hm) (spacing p S hm) (shift p S hm)

theorem input_sites : (Parameters.sourceInput p S hm).J = sites p S hm := by
  rw [Parameters.sourceInput]

theorem input_nnz : (Parameters.sourceInput p S hm).m = S.nnz := by
  rw [Parameters.sourceInput]

theorem sites_pos (hb : S.source ≠ 0) : 0 < sites p S hm := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, S.source i ≠ 0 := by
    simpa only [Function.ne_iff, Pi.zero_apply] using hb
  have hn : Nonempty (SourceDecoration.Vertex S (precision p S hm)) :=
    ⟨sourceInputSite S (precision p S hm) i⟩
  exact Fintype.card_pos_iff.mpr hn

theorem precision_pos : 1 ≤ precision p S hm := SelectedInput.precision_pos p S hm

theorem accuracy_pos : 0 < accuracy p S hm := (SelectedInput.input p S hm).accuracy_pos

theorem accuracy_le_one : accuracy p S hm ≤ 1 := SelectedInput.accuracy_le_one p S hm

theorem source_condition (hm2 : 2 ≤ S.nnz) (hp : Source.Promises p S) :
    (S.nnz : ℝ)*Maxwell.condition₂ (Source.realMatrix S) ≤ (kappa p S hm : ℝ) :=
  Maxwell.Realization.promise_logicalScale p S hm2 hp

theorem precision_budget : (S.nnz : ℝ)/(2*2^(precision p S hm)) ≤
    (accuracy p S hm : ℝ)/(64*(kappa p S hm : ℝ)) := SelectedInput.precision_budget p S hm

theorem rounding_small (hm2 : 2 ≤ S.nnz) (hp : Source.Promises p S) :
    ((S.nnz : ℝ)*Maxwell.condition₂ (Source.realMatrix S))*
      ((S.nnz : ℝ)/(2*2^(precision p S hm))) ≤ 1/2 :=
  SourceSubdivision.rounding_small S (precision p S hm) (kappa p S hm) (accuracy p S hm)
    (kappa_ge_one p S hm) (by exact_mod_cast accuracy_le_one p S hm)
    (source_condition p S hm hm2 hp) (precision_budget p S hm)

theorem budget_eq : (budget p S hm : ℝ) =
    SourceMediator.inverseBudget S (precision p S hm) (kappa p S hm) := by
  change ((Parameters.sourceInput p S hm).K : ℝ) = _
  rw [Parameters.sourceInput]
  exact PhysicalParameters.logicalInverseBudget_cast S (precision p S hm) (kappa p S hm)

theorem epsilon_eq : epsilon p S hm =
    PhysicalAccuracy.epsilon S (precision p S hm) (accuracy p S hm)/16 := by
  unfold epsilon
  rw [Parameters.sourceInput]
  rfl

theorem centers_eq : centers p S hm =
    fun i => CellGauge.latticeShift (Parameters.sourceCell p S hm (stage p S hm) i) :=
  (source_centers_shift p S hm (stage p S hm)).symm

theorem centers_disjoint : Pairwise fun i j =>
    Disjoint (Metric.ball (centers p S hm i) (length p S hm : ℝ))
      (Metric.ball (centers p S hm j) (length p S hm : ℝ)) := by
  rw [centers_eq]
  exact source_centers_disjoint p S hm (stage p S hm)

theorem centers_buffered (i : SourceDecoration.Vertex S (precision p S hm)) (j : Fin 3) :
    (buffer p S hm : ℝ)+(length p S hm : ℝ)+8 ≤ centers p S hm i j ∧
    centers p S hm i j ≤ BoxCutoff.side (box p S hm) j-
      (buffer p S hm : ℝ)-(length p S hm : ℝ)-8 := by
  rw [centers_eq]
  simpa only [buffer, Nat.cast_mul] using
    source_centers_buffered p S hm (stage p S hm) i j

theorem box_count : (∏ j, box p S hm j) ≤ count p S hm :=
  Parameters.sourceBox_count p S hm (stage p S hm)

theorem box_sides : BoxCutoff.side (box p S hm) =
    fun j => (Parameters.sourcePhysicalLengths p S hm j : ℝ) := by
  funext j
  simp only [BoxCutoff.side, Parameters.sourcePhysicalLengths, Nat.cast_mul, Nat.cast_ofNat]

theorem interaction_tail : (sites p S hm : ℝ)*Cs*(length p S hm : ℝ)^5*
    Real.exp (-cs*(length p S hm : ℝ)) ≤ (zeta p S hm : ℝ)^2/4 := by
  have h := (Parameters.source_exponential_budgets p S hm).2.2
  rw [input_sites] at h
  exact h

theorem single_interaction_tail (hb : S.source ≠ 0) :
    Cs*(length p S hm : ℝ)^5*Real.exp (-cs*(length p S hm : ℝ)) ≤ (zeta p S hm : ℝ)^2/4 := by
  have hJ : (1 : ℝ) ≤ sites p S hm := by exact_mod_cast sites_pos p S hm hb
  have hpos : 0 ≤ Cs*(length p S hm : ℝ)^5*Real.exp (-cs*(length p S hm : ℝ)) := by
    have := Cs_pos
    positivity
  calc
    _ ≤ (sites p S hm : ℝ)*(Cs*(length p S hm : ℝ)^5*Real.exp (-cs*(length p S hm : ℝ))) :=
      le_mul_of_one_le_left hpos hJ
    _ = (sites p S hm : ℝ)*Cs*(length p S hm : ℝ)^5*Real.exp (-cs*(length p S hm : ℝ)) := by ring
    _ ≤ _ := interaction_tail p S hm

theorem residual_exponentials :
    BoxCutoff.globalMajorant (∏ j, box p S hm j) (sites p S hm) S.nnz
      (budget p S hm) (alpha p S hm) (length p S hm)*
      (Real.exp (-cs*(length p S hm : ℝ)^(1/3 : ℝ))+
        Real.exp (-cs*(buffer p S hm : ℝ)/(length p S hm : ℝ))) ≤ (residual p S hm : ℝ)/2 := by
  have ht := Parameters.source_exponential_budgets p S hm
  dsimp only at ht
  rw [input_sites, input_nnz] at ht
  change BoxCutoff.globalMajorant (count p S hm) (sites p S hm) S.nnz
      (budget p S hm) (alpha p S hm) (length p S hm)*
      Real.exp (-cs*(length p S hm : ℝ)^(1/3 : ℝ)) ≤ (residual p S hm : ℝ)/4 ∧
    BoxCutoff.globalMajorant (count p S hm) (sites p S hm) S.nnz
      (budget p S hm) (alpha p S hm) (length p S hm)*
      Real.exp (-cs*((length p S hm : ℝ)*(bufferSteps p S hm : ℝ))/(length p S hm : ℝ)) ≤
        (residual p S hm : ℝ)/4 ∧ _ at ht
  have hN : ((∏ j, box p S hm j : ℕ) : ℝ) ≤ count p S hm := by exact_mod_cast box_count p S hm
  have hmajor : BoxCutoff.globalMajorant (∏ j, box p S hm j) (sites p S hm) S.nnz
      (budget p S hm) (alpha p S hm) (length p S hm) ≤
      BoxCutoff.globalMajorant (count p S hm) (sites p S hm) S.nnz
        (budget p S hm) (alpha p S hm) (length p S hm) := by
    have hCs := Cs_pos.le
    have hK := (budget_ge_one p S hm).trans' zero_le_one
    have hα := (alpha_pos p S hm).le
    unfold BoxCutoff.globalMajorant BoxCutoff.residualEnvelope
    gcongr
    simpa only [Nat.cast_prod] using hN
  have hmul := mul_le_mul_of_nonneg_right hmajor
    (show 0 ≤ Real.exp (-cs*(length p S hm : ℝ)^(1/3 : ℝ))+
      Real.exp (-cs*(buffer p S hm : ℝ)/(length p S hm : ℝ)) by positivity)
  apply hmul.trans
  simp only [mul_add, buffer, Nat.cast_mul]
  linarith only [ht.1, ht.2.1]

#print axioms rounding_small
#print axioms centers_buffered
#print axioms residual_exponentials

end Maxwell.Continuum.RealizationParameters
