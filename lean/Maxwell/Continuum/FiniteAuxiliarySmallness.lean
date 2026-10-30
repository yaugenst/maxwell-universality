import Maxwell.Continuum.FiniteAuxiliaryComplement
import Maxwell.Continuum.FiniteAuxiliaryMixed
import Maxwell.Continuum.ParameterAssembly

/-! The paper's scalar tests imply invertibility of the actual complete
complement and control both mixed blocks. No complementary inverse or
operator smallness premise remains. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.FiniteAuxiliary

open Auxiliary EffectiveMass MasterConstants

attribute [local irreducible] realMode Sh muH Cs

variable {ι : Type*} [Fintype ι]

theorem placed_modeGap {L : ℕ} : modeGap (L : ℝ)⁻¹ = (1/(2 : ℝ)^192)*(L : ℝ)^2 := by
  rw [modeGap, inv_pow, inv_inv, one_div]

theorem assembly_complement_small {L d : ℕ} {z σ ε : ℝ}
    (hL : Ls ≤ (L : ℝ)) (D : Calibration (L : ℝ)⁻¹ z)
    (hh : (L : ℝ)⁻¹ ≤ 1/(2 : ℝ)^1024)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ ((L : ℝ)⁻¹)^4/64) (hd : 1 ≤ d)
    (position : ι → Bloch.Alias) (hinj : Function.Injective position) (v : ι → ℝ)
    (hε : ε ≤ 1)
    (hfirst : Cs^4*(L : ℝ)^12*((3 : ℝ)^d)⁻¹ ≤ ε/(2 : ℝ)^24)
    (hv : ∀ i, |(v i)⁻¹-muH D hh| ≤ (1/(2 : ℝ)^196)*(L : ℝ)^2+(((3 : ℝ)^d)⁻¹)^2)
    (htail : (Fintype.card ι : ℝ)*Cs*(L : ℝ)^5*Real.exp (-cs*(L : ℝ)) ≤ (((3 : ℝ)^d)⁻¹)^2/4)
    (hdt : 16*σ*(L : ℝ)^4 ≤ (((3 : ℝ)^d)⁻¹)^2/(2 : ℝ)^20) :
    ‖auxiliaryMatrix D hσ0 hσ (centers L d position) v-baseline D hh‖ ≤
      modeGap (L : ℝ)⁻¹/2 := by
  have hb := (Parameters.assembly_scalar_budgets hL (by positivity) hε hfirst le_rfl htail hdt).1
  apply actual_complement_perturbation hL D hh hσ0 hσ hd position hinj v (by positivity) hv
  have hp : (((L : ℝ)⁻¹)^4)⁻¹ = (L : ℝ)^4 := by simp only [inv_pow, inv_inv]
  rw [placed_modeGap, hp]
  convert hb using 1
  ring

theorem assembly_coupling_small {L d : ℕ} {z σ ε : ℝ}
    (hL : Ls ≤ (L : ℝ)) (D : Calibration (L : ℝ)⁻¹ z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ ((L : ℝ)⁻¹)^4/64) (hd : 1 ≤ d)
    (position : ι → Bloch.Alias) (hinj : Function.Injective position)
    (hε : ε ≤ 1)
    (hfirst : Cs^4*(L : ℝ)^12*((3 : ℝ)^d)⁻¹ ≤ ε/(2 : ℝ)^24)
    (htail : (Fintype.card ι : ℝ)*Cs*(L : ℝ)^5*Real.exp (-cs*(L : ℝ)) ≤ (((3 : ℝ)^d)⁻¹)^2/4)
    (hdt : 16*σ*(L : ℝ)^4 ≤ (((3 : ℝ)^d)⁻¹)^2/(2 : ℝ)^20) :
    ‖couplingError D hσ0 hσ d position‖ ≤ 128*(Cs*(L : ℝ)^5)*((3 : ℝ)^d)⁻¹ ∧
    ‖couplingError D hσ0 hσ d position‖*((2 : ℝ)^194*((L : ℝ)⁻¹)^2) ≤ 1 := by
  have hb := (Parameters.assembly_scalar_budgets hL (by positivity) hε hfirst
    (le_refl ((1/(2 : ℝ)^196)*(L : ℝ)^2+(((3 : ℝ)^d)⁻¹)^2)) htail hdt).2
  have he := couplingError_norm hL D hσ0 hσ hd position hinj
  rw [inv_pow, inv_inv] at he
  have hn : ‖couplingError D hσ0 hσ d position‖ ≤
      64*(Cs*(L : ℝ)^5)*((3 : ℝ)^d)⁻¹+
      (Fintype.card ι : ℝ)*Cs*(L : ℝ)^5*Real.exp (-cs*(L : ℝ))+16*σ*(L : ℝ)^4 := by
    convert he using 1
    ring
  exact ⟨hn.trans hb.1, (mul_le_mul_of_nonneg_right hn (by positivity)).trans hb.2⟩

#print axioms assembly_complement_small
#print axioms assembly_coupling_small

end Maxwell.Continuum.FiniteAuxiliary
