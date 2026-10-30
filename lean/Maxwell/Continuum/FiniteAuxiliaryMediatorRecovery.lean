import Maxwell.Continuum.FiniteAuxiliaryLogical

/-! The actual finite mediator elimination bound on complex bright
coordinates. Real and imaginary parts satisfy the same real construction,
and their squared norms add exactly. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.FiniteAuxiliary

open Maxwell.Composition ComplexInverse

variable {V E : Type*} [Fintype V] [Fintype E]

def complexTerminalInjection (g : EuclideanSpace ℂ V) : EuclideanSpace ℂ (V ⊕ E) :=
  WithLp.toLp 2 (Sum.elim g (fun _ => 0))

def complexTerminalPart (z : EuclideanSpace ℂ (V ⊕ E)) : EuclideanSpace ℂ V :=
  WithLp.toLp 2 (fun i => z (Sum.inl i))

theorem complexTerminalInjection_norm (g : EuclideanSpace ℂ V) :
    ‖complexTerminalInjection (E := E) g‖ = ‖g‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp [EuclideanSpace.norm_sq_eq, complexTerminalInjection, Fintype.sum_sum_type]

theorem realPart_sub {ι : Type*} [Fintype ι] (a b : EuclideanSpace ℂ ι) :
    realPart (a-b) = realPart a-realPart b := by ext i; rfl

theorem imagPart_sub {ι : Type*} [Fintype ι] (a b : EuclideanSpace ℂ ι) :
    imagPart (a-b) = imagPart a-imagPart b := by ext i; rfl

theorem realPart_real_smul {ι : Type*} [Fintype ι] (c : ℝ) (a : EuclideanSpace ℂ ι) :
    realPart ((c : ℂ) • a) = c • realPart a := by
  ext i
  change ((c : ℂ)*a i).re = c*(a i).re
  simp

theorem imagPart_real_smul {ι : Type*} [Fintype ι] (c : ℝ) (a : EuclideanSpace ℂ ι) :
    imagPart ((c : ℂ) • a) = c • imagPart a := by
  ext i
  change ((c : ℂ)*a i).im = c*(a i).im
  simp

variable [DecidableEq V] [DecidableEq E]

theorem complex_mediator_residual (G : SignedIncidence V E) (α : ℝ) (β : E → ℝ)
    (diag : V → ℝ) (hα : 0 < α) (hβ : ∀ e, 3*α ≤ |β e|) (hdeg : ∀ i, G.degree i ≤ 3)
    (z : EuclideanSpace ℂ (V ⊕ E)) (g : EuclideanSpace ℂ V) :
    ‖complexOperator (G.logicalMatrix diag) (complexTerminalPart z)-g‖ ≤
      (4/α)*‖logicalTarget G α β diag z-(α : ℂ) • complexTerminalInjection g‖ := by
  have hr := G.target_residual_transfer α β diag hα hβ hdeg (realPart z) (realPart g)
  have hi := G.target_residual_transfer α β diag hα hβ hdeg (imagPart z) (imagPart g)
  have hlr : realPart (complexTerminalPart z) = sumLeftProjection (realPart z) := by ext i; rfl
  have hli : imagPart (complexTerminalPart z) = sumLeftProjection (imagPart z) := by ext i; rfl
  have hgr : realPart (complexTerminalInjection (E := E) g) = sumLeftInjection (realPart g) := by
    ext i
    cases i <;> rfl
  have hgi : imagPart (complexTerminalInjection (E := E) g) = sumLeftInjection (imagPart g) := by
    ext i
    cases i <;> rfl
  have her : realPart (complexOperator (G.logicalMatrix diag) (complexTerminalPart z)-g) =
      realOperator (G.logicalMatrix diag) (sumLeftProjection (realPart z))-realPart g := by
    rw [realPart_sub, complexOperator_realPart, hlr]
  have hei : imagPart (complexOperator (G.logicalMatrix diag) (complexTerminalPart z)-g) =
      realOperator (G.logicalMatrix diag) (sumLeftProjection (imagPart z))-imagPart g := by
    rw [imagPart_sub, complexOperator_imagPart, hli]
  have hfr : ComplexInverse.realPart (logicalTarget G α β diag z-(α : ℂ) • complexTerminalInjection g) =
      G.targetOperator α β diag (realPart z)-α • sumLeftInjection (realPart g) := by
    rw [realPart_sub, logicalTarget, complexOperator_realPart, realPart_real_smul, hgr]
    rfl
  have hfi : imagPart (logicalTarget G α β diag z-(α : ℂ) • complexTerminalInjection g) =
      G.targetOperator α β diag (imagPart z)-α • sumLeftInjection (imagPart g) := by
    rw [imagPart_sub, logicalTarget, complexOperator_imagPart, imagPart_real_smul, hgi]
    rfl
  dsimp only [realOperator] at her hei
  rw [← her, ← hfr] at hr
  rw [← hei, ← hfi] at hi
  have hrs := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hr
  have his := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hi
  have hs := norm_sq_parts (complexOperator (G.logicalMatrix diag) (complexTerminalPart z)-g)
  have ht := norm_sq_parts (logicalTarget G α β diag z-(α : ℂ) • complexTerminalInjection g)
  have hscaled := congrArg (fun x : ℝ => (4/α)^2*x) ht
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  nlinarith only [hrs, his, hs, hscaled]

#print axioms complex_mediator_residual

end Maxwell.Continuum.FiniteAuxiliary
