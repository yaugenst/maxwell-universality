import Maxwell.Continuum.FiniteAuxiliaryIdealSource
import Maxwell.Continuum.FiniteAuxiliarySmallness
import Maxwell.Continuum.ParameterSourceForcing

/-! The literal ideal source produces the intended bright forcing, with
the actual off-site interactions and detuning retained in its error. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048

namespace Maxwell.Continuum.FiniteAuxiliary

open Auxiliary EffectiveMass Bloch MasterConstants

attribute [local irreducible] Auxiliary.resolvent realMode Sh muH Qh Cs

variable {ι : Type*} [Fintype ι]

theorem compressed_sigma_decomposition {L : ℕ} {z σ : ℝ}
    (D : Calibration (L : ℝ)⁻¹ z) (hσ0 : 0 ≤ σ) (hσ : σ ≤ (L : ℝ)⁻¹^4/64)
    (d : ℕ) (position : ι → Alias) (hinj : Function.Injective position) :
    compressed (L : ℝ)⁻¹ (centers L d position) (resolvent D hσ0 hσ) =
      diagonalBlocks (fun _ : ι => Sh D)+couplingError D hσ0 hσ d position := by
  rw [couplingError, compressed_zero_decomposition D d position hinj]
  abel

omit [Fintype ι] in
theorem diagonalSh_bright {h z : ℝ} (D : Calibration h z) (hh : h ≤ 1/(2 : ℝ)^1024)
    (g : BrightSpace ι) :
    diagonalBlocks (fun _ : ι => Sh D) (bright (realMode D hh) g) =
      (muH D hh : ℂ) • bright (realMode D hh) g := by
  apply PiLp.ext
  intro i
  change Sh D (g i • realMode D hh) = (muH D hh : ℂ) • (g i • realMode D hh)
  rw [map_smul, realMode_eigen, smul_comm]

theorem idealSource_forcing_identity {L : ℕ} {z σ : ℝ}
    (D : Calibration (L : ℝ)⁻¹ z) (hh : (L : ℝ)⁻¹ ≤ 1/(2 : ℝ)^1024)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ (L : ℝ)⁻¹^4/64)
    (d : ℕ) (position : ι → Alias) (hinj : Function.Injective position)
    (α : ℝ) (g : BrightSpace ι) :
    collection (L : ℝ)⁻¹ (centers L d position)
      (resolvent D hσ0 hσ (idealSource D hh (centers L d position) α g)) =
      (α : ℂ) • bright (realMode D hh) g+
        ((α/muH D hh : ℝ) : ℂ) • couplingError D hσ0 hσ d position (bright (realMode D hh) g) := by
  have hc := congrArg (fun T : DefectSpace ι →L[ℂ] DefectSpace ι => T (bright (realMode D hh) g))
    (compressed_sigma_decomposition D hσ0 hσ d position hinj)
  simp only [compressed, ContinuousLinearMap.comp_apply, collection_adjoint, add_apply] at hc
  rw [idealSource_eq, map_smul, map_smul, hc, diagonalSh_bright, smul_add, smul_smul,
    ← Complex.ofReal_mul, div_mul_cancel₀ _ (muH_pos D hh).ne']

theorem idealSource_forcing_error {L : ℕ} {z σ α : ℝ}
    (D : Calibration (L : ℝ)⁻¹ z) (hh : (L : ℝ)⁻¹ ≤ 1/(2 : ℝ)^1024)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ (L : ℝ)⁻¹^4/64)
    (d : ℕ) (position : ι → Alias) (hinj : Function.Injective position) (hα : 0 ≤ α)
    (g : BrightSpace ι) :
    ‖collection (L : ℝ)⁻¹ (centers L d position)
      (resolvent D hσ0 hσ (idealSource D hh (centers L d position) α g))-
      (α : ℂ) • bright (realMode D hh) g‖ ≤
      α*((2 : ℝ)^128*(L : ℝ)⁻¹^2)*‖couplingError D hσ0 hσ d position‖*‖g‖ := by
  have hp := muH_pos D hh
  rw [idealSource_forcing_identity D hh hσ0 hσ d position hinj α g, add_sub_cancel_left,
    norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  calc
    _ ≤ (α/muH D hh)*(‖couplingError D hσ0 hσ d position‖*‖bright (realMode D hh) g‖) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (by positivity)
    _ ≤ (α*((2 : ℝ)^128*(L : ℝ)⁻¹^2))*(‖couplingError D hσ0 hσ d position‖*‖g‖) := by
      rw [bright_norm _ (realMode_norm D hh), div_eq_mul_inv]
      gcongr
      exact muH_inverse_le D hh
    _ = _ := by ring

theorem idealSource_forcing_budget {L d : ℕ} {z σ α ε : ℝ}
    (hL : Ls ≤ (L : ℝ)) (D : Calibration (L : ℝ)⁻¹ z)
    (hh : (L : ℝ)⁻¹ ≤ 1/(2 : ℝ)^1024)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ ((L : ℝ)⁻¹)^4/64) (hd : 1 ≤ d)
    (position : ι → Alias) (hinj : Function.Injective position)
    (hε : ε ≤ 1) (hα : 0 ≤ α)
    (hfirst : Cs^4*(L : ℝ)^12*((3 : ℝ)^d)⁻¹ ≤ ε/(2 : ℝ)^24)
    (htail : (Fintype.card ι : ℝ)*Cs*(L : ℝ)^5*Real.exp (-cs*(L : ℝ)) ≤ (((3 : ℝ)^d)⁻¹)^2/4)
    (hdt : 16*σ*(L : ℝ)^4 ≤ (((3 : ℝ)^d)⁻¹)^2/(2 : ℝ)^20)
    (g : BrightSpace ι) :
    ‖collection (L : ℝ)⁻¹ (centers L d position)
      (resolvent D hσ0 hσ (idealSource D hh (centers L d position) α g))-
      (α : ℂ) • bright (realMode D hh) g‖ ≤ α*ε*‖g‖/(2 : ℝ)^24 := by
  have hc := (assembly_coupling_small hL D hσ0 hσ hd position hinj hε hfirst htail hdt).1
  have hp := Parameters.source_forcing_budget hL (by positivity) hfirst
  apply (idealSource_forcing_error D hh hσ0 hσ d position hinj hα g).trans
  calc
    _ ≤ α*(((2 : ℝ)^128*(L : ℝ)⁻¹^2)*(128*(Cs*(L : ℝ)^5)*((3 : ℝ)^d)⁻¹))*‖g‖ := by
      have ht := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hc (show 0 ≤ α*((2 : ℝ)^128*(L : ℝ)⁻¹^2) by positivity))
        (norm_nonneg g)
      convert ht using 1
      ring
    _ ≤ α*(ε/(2 : ℝ)^24)*‖g‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg g)
      apply mul_le_mul_of_nonneg_left _ hα
      convert hp using 1
      ring
    _ = _ := by ring

#print axioms idealSource_forcing_identity
#print axioms idealSource_forcing_error
#print axioms idealSource_forcing_budget

end Maxwell.Continuum.FiniteAuxiliary
