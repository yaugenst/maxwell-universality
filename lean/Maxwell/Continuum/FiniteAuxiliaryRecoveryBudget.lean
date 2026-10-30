import Maxwell.Continuum.FiniteAuxiliaryMediatorRecovery

/-! Quantitative bright and logical recovery, retaining the complete
forcing residual and the full reduced-operator perturbation. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.FiniteAuxiliary

section Bright
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

theorem brightResponse_amplitude (S : H ≃L[ℂ] H) {α ε K : ℝ}
    (hα : 0 < α) (_hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hK : 1 ≤ K)
    (hS : ‖(S.symm : H →L[ℂ] H)‖ ≤ 32*K/α) (z g : H)
    (hr : ‖S z-(α : ℂ) • g‖ ≤ α*ε*‖g‖/(2 : ℝ)^23) : ‖z‖ ≤ 33*K*‖g‖ := by
  have hKn : 0 ≤ K := zero_le_one.trans hK
  have hz := (S.symm : H →L[ℂ] H).le_of_opNorm_le hS (S z)
  simp only [ContinuousLinearEquiv.coe_coe, S.symm_apply_apply] at hz
  have hn : ‖S z‖ ≤ α*ε*‖g‖/(2 : ℝ)^23+α*‖g‖ := by
    have ht := norm_add_le (S z-(α : ℂ) • g) ((α : ℂ) • g)
    rw [sub_add_cancel, norm_smul, Complex.norm_real, Real.norm_of_nonneg hα.le] at ht
    exact ht.trans (add_le_add hr le_rfl)
  calc
    _ ≤ (32*K/α)*(α*ε*‖g‖/(2 : ℝ)^23+α*‖g‖) :=
      hz.trans (mul_le_mul_of_nonneg_left hn (by positivity))
    _ = (32+ε/(2 : ℝ)^18)*K*‖g‖ := by field_simp; ring
    _ ≤ 33*K*‖g‖ := by
      gcongr
      have he := div_le_div_of_nonneg_right hε1 (by positivity : 0 ≤ (2 : ℝ)^18)
      norm_num at he ⊢
      linarith only [he]

theorem brightResponse_target_budget (S : H ≃L[ℂ] H) (Θ : H →L[ℂ] H) {α ε K : ℝ}
    (hα : 0 < α) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hK : 1 ≤ K)
    (hS : ‖(S.symm : H →L[ℂ] H)‖ ≤ 32*K/α)
    (hΘ : ‖(S : H →L[ℂ] H)-Θ‖ ≤ α*ε/((2 : ℝ)^24*K)) (z g : H)
    (hr : ‖S z-(α : ℂ) • g‖ ≤ α*ε*‖g‖/(2 : ℝ)^23) :
    ‖Θ z-(α : ℂ) • g‖ ≤ α*ε*‖g‖/4096 := by
  have hKp : 0 < K := zero_lt_one.trans_le hK
  have hz := brightResponse_amplitude S hα hε hε1 hK hS z g hr
  have hp := ((S : H →L[ℂ] H)-Θ).le_of_opNorm_le hΘ z
  have he : Θ z-(α : ℂ) • g = (S z-(α : ℂ) • g)-(((S : H →L[ℂ] H)-Θ) z) := by
    change Θ z-(α : ℂ) • g = (S z-(α : ℂ) • g)-(S z-Θ z)
    abel
  rw [he]
  calc
    _ ≤ ‖S z-(α : ℂ) • g‖+‖((S : H →L[ℂ] H)-Θ) z‖ := norm_sub_le _ _
    _ ≤ α*ε*‖g‖/(2 : ℝ)^23+(α*ε/((2 : ℝ)^24*K))*(33*K*‖g‖) :=
      add_le_add hr (hp.trans (mul_le_mul_of_nonneg_left hz (by positivity)))
    _ = (35/(2 : ℝ)^24)*(α*ε*‖g‖) := by field_simp; ring
    _ ≤ α*ε*‖g‖/4096 := by
      have hc : (35/(2 : ℝ)^24) ≤ 1/4096 := by norm_num
      simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using
        mul_le_mul_of_nonneg_right hc (show 0 ≤ α*ε*‖g‖ by positivity)

end Bright

open Maxwell.Composition ComplexInverse

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

theorem brightResponse_logical_budget (G : SignedIncidence V E) (α : ℝ) (β : E → ℝ)
    (diag : V → ℝ) {ε K : ℝ} (hα : 0 < α) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hK : 1 ≤ K)
    (hβ : ∀ e, 3*α ≤ |β e|) (hdeg : ∀ i, G.degree i ≤ 3)
    (S : EuclideanSpace ℂ (V ⊕ E) ≃L[ℂ] EuclideanSpace ℂ (V ⊕ E))
    (hS : ‖(S.symm : EuclideanSpace ℂ (V ⊕ E) →L[ℂ] EuclideanSpace ℂ (V ⊕ E))‖ ≤ 32*K/α)
    (hΘ : ‖(S : EuclideanSpace ℂ (V ⊕ E) →L[ℂ] EuclideanSpace ℂ (V ⊕ E))-
      logicalTarget G α β diag‖ ≤ α*ε/((2 : ℝ)^24*K))
    (z : EuclideanSpace ℂ (V ⊕ E)) (g : EuclideanSpace ℂ V)
    (hr : ‖S z-(α : ℂ) • complexTerminalInjection g‖ ≤ α*ε*‖g‖/(2 : ℝ)^23) :
    ‖complexOperator (G.logicalMatrix diag) (complexTerminalPart z)-g‖ ≤ ε*‖g‖/1024 := by
  have hr' : ‖S z-(α : ℂ) • complexTerminalInjection g‖ ≤
      α*ε*‖complexTerminalInjection (E := E) g‖/(2 : ℝ)^23 := by
    simpa only [complexTerminalInjection_norm] using hr
  have hb := brightResponse_target_budget S (logicalTarget G α β diag) hα hε hε1 hK hS hΘ
    z (complexTerminalInjection g) hr'
  rw [complexTerminalInjection_norm] at hb
  apply (complex_mediator_residual G α β diag hα hβ hdeg z g).trans
  apply (mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 4/α)).trans_eq
  field_simp
  ring

#print axioms brightResponse_logical_budget

end Maxwell.Continuum.FiniteAuxiliary
