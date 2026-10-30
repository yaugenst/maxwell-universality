import Maxwell.Continuum.FiniteAuxiliaryBrightRaw
import Maxwell.Continuum.FiniteAuxiliarySchurBounds
import Maxwell.Continuum.ParameterAssemblyError

/-! The full bright Schur error of the routed continuum wells satisfies
the paper's squared-spacing bound. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.FiniteAuxiliary

open Auxiliary EffectiveMass MasterConstants Maxwell.Composition

attribute [local irreducible] realMode Sh muH Cs

variable (S : Source.SparseSystem) (precision : ℕ)
local instance : DecidableEq (SourceIncidence.V S precision) := Classical.decEq _

theorem source_reduced_error {L d : ℕ} {z σ ε : ℝ}
    (hL : Ls ≤ (L : ℝ)) (D : Calibration (L : ℝ)⁻¹ z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ ((L : ℝ)⁻¹)^4/64) (hd : 1 ≤ d)
    (v : SourceDecoration.Vertex S precision → ℝ) (α : ℝ) (β : Fin 3 → ℝ)
    (diag : SourceIncidence.V S precision → ℝ)
    (hM : ‖auxiliaryMatrix D hσ0 hσ (centers L d (SourceDecoration.site S precision)) v-
      baseline D (inverse_length_le_1024 hL)‖ ≤ modeGap (L : ℝ)⁻¹/2)
    (hε : ε ≤ 1)
    (hfirst : Cs^4*(L : ℝ)^12*((3 : ℝ)^d)⁻¹ ≤ ε/(2 : ℝ)^24)
    (hv : ∀ i, |(v i)⁻¹-(muH D (inverse_length_le_1024 hL)+
      (SourceIncidence.graph S precision).targetMatrix α
        (fun e => β (SourceIncidence.axis S precision e)) diag i i)| ≤ (((3 : ℝ)^d)⁻¹)^2)
    (hβ : ∀ j, |β j+usefulCoupling hL D d j| ≤ (((3 : ℝ)^d)⁻¹)^2/16)
    (htail : (Fintype.card (SourceDecoration.Vertex S precision) : ℝ)*Cs*(L : ℝ)^5*
      Real.exp (-cs*(L : ℝ)) ≤ (((3 : ℝ)^d)⁻¹)^2/4)
    (hdt : 16*σ*(L : ℝ)^4 ≤ (((3 : ℝ)^d)⁻¹)^2/(2 : ℝ)^20) :
    ‖reducedMatrix D (inverse_length_le_1024 hL)
      (auxiliaryMatrix D hσ0 hσ (centers L d (SourceDecoration.site S precision)) v) hM-
      logicalTarget (SourceIncidence.graph S precision) α
        (fun e => β (SourceIncidence.axis S precision e)) diag‖ ≤
      Cs^4*(L : ℝ)^12*(((3 : ℝ)^d)⁻¹)^2 := by
  let p := SourceDecoration.site S precision
  let hh := inverse_length_le_1024 hL
  have hraw := source_raw_bright_error S precision hL D hσ0 hσ hd v α β diag
    (sq_nonneg _) (by positivity) hv hβ
  have he := reducedMatrix_error D hh hσ0 hσ d p (SourceDecoration.site_injective S precision) v hM
    (logicalTarget (SourceIncidence.graph S precision) α
      (fun e => β (SourceIncidence.axis S precision e)) diag) hraw
  have hc := (assembly_coupling_small hL D hσ0 hσ hd p
    (SourceDecoration.site_injective S precision) hε hfirst htail hdt).1
  have hsq := pow_le_pow_left₀ (norm_nonneg (couplingError D hσ0 hσ d p)) hc 2
  have hcor := mul_le_mul_of_nonneg_right hsq
    (show 0 ≤ (2 : ℝ)^194*((L : ℝ)⁻¹)^2 by positivity)
  have hb := Parameters.assembly_bright_error hL htail hdt
  apply he.trans
  calc
    _ ≤ (((3 : ℝ)^d)⁻¹)^2+3*((((3 : ℝ)^d)⁻¹)^2/16)+
        (256*(Cs*(L : ℝ)^5)*(((3 : ℝ)^d)⁻¹)^2+
          (Fintype.card (SourceDecoration.Vertex S precision) : ℝ)*Cs*(L : ℝ)^5*
            Real.exp (-cs*(L : ℝ)))+16*σ*(L : ℝ)^4+
        (128*(Cs*(L : ℝ)^5)*((3 : ℝ)^d)⁻¹)^2*((2 : ℝ)^194*((L : ℝ)⁻¹)^2) := by
      convert add_le_add_left hcor
        ((((3 : ℝ)^d)⁻¹)^2+3*((((3 : ℝ)^d)⁻¹)^2/16)+
          Cs*(L : ℝ)^5*(256*(((3 : ℝ)^d)⁻¹)^2+
            (Fintype.card (SourceDecoration.Vertex S precision) : ℝ)*Real.exp (-cs*(L : ℝ)))+
          16*σ*(L : ℝ)^4) using 1 <;> ring
    _ ≤ _ := hb

#print axioms source_reduced_error

end Maxwell.Continuum.FiniteAuxiliary
