import Maxwell.Continuum.FiniteAuxiliarySourceForcing
import Maxwell.Continuum.FiniteAuxiliarySourceSchur
import Maxwell.Continuum.FiniteAuxiliaryRecoveryBudget
import Maxwell.Continuum.FiniteAuxiliaryStable

/-! Bright-coordinate recovery for the actual ideal-source Maxwell
construction. Both the forcing defect and the reduced-operator error
come from the continuum assembly, with the selected scalar tests. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048
set_option maxHeartbeats 800000

namespace Maxwell.Continuum.FiniteAuxiliary

open Auxiliary EffectiveMass Bloch MasterConstants Maxwell.Composition

attribute [local irreducible] Auxiliary.resolvent realMode Sh muH Qh Cs

variable {ι : Type*} [Fintype ι]

theorem idealSource_bright_residual {L d : ℕ} {z σ α ε : ℝ}
    (hL : Ls ≤ (L : ℝ)) (D : Calibration (L : ℝ)⁻¹ z)
    (hh : (L : ℝ)⁻¹ ≤ 1/(2 : ℝ)^1024)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ ((L : ℝ)⁻¹)^4/64) (hd : 1 ≤ d)
    (position : ι → Alias) (hinj : Function.Injective position) (v : ι → ℝ)
    (hε : ε ≤ 1) (hα : 0 ≤ α)
    (hfirst : Cs^4*(L : ℝ)^12*((3 : ℝ)^d)⁻¹ ≤ ε/(2 : ℝ)^24)
    (htail : (Fintype.card ι : ℝ)*Cs*(L : ℝ)^5*Real.exp (-cs*(L : ℝ)) ≤ (((3 : ℝ)^d)⁻¹)^2/4)
    (hdt : 16*σ*(L : ℝ)^4 ≤ (((3 : ℝ)^d)⁻¹)^2/(2 : ℝ)^20)
    (hM : ‖auxiliaryMatrix D hσ0 hσ (centers L d position) v-baseline D hh‖ ≤ modeGap (L : ℝ)⁻¹/2)
    (A : DefectSpace ι ≃L[ℂ] DefectSpace ι)
    (hA : (A : DefectSpace ι →L[ℂ] DefectSpace ι) = auxiliaryMatrix D hσ0 hσ (centers L d position) v)
    (g : BrightSpace ι) :
    ‖reducedMatrix D hh (auxiliaryMatrix D hσ0 hσ (centers L d position) v) hM
      (brightResponse D hh hσ0 hσ (centers L d position) A
        (idealSource D hh (centers L d position) α g))-(α : ℂ) • g‖ ≤ α*ε*‖g‖/(2 : ℝ)^23 := by
  have hmixed := (assembly_coupling_small hL D hσ0 hσ hd position hinj hε hfirst htail hdt).2
  have hn := reducedResidual_norm D hh hσ0 hσ d position hinj v hM hmixed
  have hf := idealSource_forcing_budget hL D hh hσ0 hσ hd position hinj hε hα hfirst htail hdt g
  rw [brightResponse_residual_identity D hh hσ0 hσ (centers L d position) v A hA hM]
  apply ((reducedResidual D hh (auxiliaryMatrix D hσ0 hσ (centers L d position) v) hM).le_of_opNorm_le hn _).trans
  apply (mul_le_mul_of_nonneg_left hf (by norm_num : (0 : ℝ) ≤ 2)).trans_eq
  norm_num
  ring

variable (S : Source.SparseSystem) (precision : ℕ)
local instance : DecidableEq (SourceIncidence.V S precision) := Classical.decEq _

theorem source_bright_logical_residual {L d : ℕ} {z σ α ε K : ℝ}
    (hL : Ls ≤ (L : ℝ)) (D : Calibration (L : ℝ)⁻¹ z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ ((L : ℝ)⁻¹)^4/64) (hd : 1 ≤ d)
    (v : SourceDecoration.Vertex S precision → ℝ) (β : Fin 3 → ℝ)
    (diag : SourceIncidence.V S precision → ℝ)
    (hK : 1 ≤ K) (hα : 0 < α) (hε0 : 0 ≤ ε) (hε : ε ≤ 1)
    (hfirst : Cs^4*(L : ℝ)^12*((3 : ℝ)^d)⁻¹ ≤ ε/(2 : ℝ)^24)
    (hsecond : Cs^4*(L : ℝ)^12*(((3 : ℝ)^d)⁻¹)^2 ≤ α*ε/((2 : ℝ)^24*K))
    (hv : ∀ i, |(v i)⁻¹-(muH D (inverse_length_le_1024 hL)+
      (SourceIncidence.graph S precision).targetMatrix α
        (fun e => β (SourceIncidence.axis S precision e)) diag i i)| ≤ (((3 : ℝ)^d)⁻¹)^2)
    (hβ : ∀ j, |β j+usefulCoupling hL D d j| ≤ (((3 : ℝ)^d)⁻¹)^2/16)
    (hβlower : ∀ j, 3*α ≤ |β j|)
    (htail : (Fintype.card (SourceDecoration.Vertex S precision) : ℝ)*Cs*(L : ℝ)^5*
      Real.exp (-cs*(L : ℝ)) ≤ (((3 : ℝ)^d)⁻¹)^2/4)
    (hdt : 16*σ*(L : ℝ)^4 ≤ (((3 : ℝ)^d)⁻¹)^2/(2 : ℝ)^20)
    (hM : ‖auxiliaryMatrix D hσ0 hσ (centers L d (SourceDecoration.site S precision)) v-
      baseline D (inverse_length_le_1024 hL)‖ ≤ modeGap (L : ℝ)⁻¹/2)
    (A : DefectSpace (SourceDecoration.Vertex S precision) ≃L[ℂ]
      DefectSpace (SourceDecoration.Vertex S precision))
    (hA : (A : DefectSpace (SourceDecoration.Vertex S precision) →L[ℂ]
      DefectSpace (SourceDecoration.Vertex S precision)) =
      auxiliaryMatrix D hσ0 hσ (centers L d (SourceDecoration.site S precision)) v)
    (T : BrightSpace (SourceDecoration.Vertex S precision) ≃L[ℂ]
      BrightSpace (SourceDecoration.Vertex S precision))
    (hT : (T : BrightSpace (SourceDecoration.Vertex S precision) →L[ℂ]
      BrightSpace (SourceDecoration.Vertex S precision)) = logicalTarget (SourceIncidence.graph S precision) α
      (fun e => β (SourceIncidence.axis S precision e)) diag)
    (hTnorm : ‖(T.symm : BrightSpace (SourceDecoration.Vertex S precision) →L[ℂ]
      BrightSpace (SourceDecoration.Vertex S precision))‖ ≤ 16*K/α)
    (g : EuclideanSpace ℂ (SourceIncidence.V S precision)) :
    ‖ComplexInverse.complexOperator ((SourceIncidence.graph S precision).logicalMatrix diag)
      (complexTerminalPart (brightResponse D (inverse_length_le_1024 hL) hσ0 hσ
        (centers L d (SourceDecoration.site S precision)) A
        (idealSource D (inverse_length_le_1024 hL) (centers L d (SourceDecoration.site S precision)) α
          (complexTerminalInjection g))))-g‖ ≤ ε*‖g‖/1024 := by
  let p := SourceDecoration.site S precision
  let hh := inverse_length_le_1024 hL
  let M := auxiliaryMatrix D hσ0 hσ (centers L d p) v
  have herr := source_reduced_error S precision hL D hσ0 hσ hd v α β diag hM hε hfirst hv hβ htail hdt
  have herrT : ‖reducedMatrix D hh M hM-(T : BrightSpace (SourceDecoration.Vertex S precision) →L[ℂ]
      BrightSpace (SourceDecoration.Vertex S precision))‖ ≤ Cs^4*(L : ℝ)^12*(((3 : ℝ)^d)⁻¹)^2 := by
    rw [hT]
    exact herr
  obtain ⟨B, hB, hnB⟩ := exists_equiv_of_assembly_budget T (reducedMatrix D hh M hM)
    hK hα hε hTnorm herrT hsecond
  have herror : ‖(B : BrightSpace (SourceDecoration.Vertex S precision) →L[ℂ]
      BrightSpace (SourceDecoration.Vertex S precision))-logicalTarget (SourceIncidence.graph S precision) α
      (fun e => β (SourceIncidence.axis S precision e)) diag‖ ≤ α*ε/((2 : ℝ)^24*K) := by
    rw [hB]
    exact herr.trans hsecond
  have hr := idealSource_bright_residual hL D hh hσ0 hσ hd p
    (SourceDecoration.site_injective S precision) v hε hα.le hfirst htail hdt hM A hA
    (complexTerminalInjection g)
  rw [complexTerminalInjection_norm] at hr
  have hrB : ‖B (brightResponse D hh hσ0 hσ (centers L d p) A
      (idealSource D hh (centers L d p) α (complexTerminalInjection g)))-
      (α : ℂ) • complexTerminalInjection g‖ ≤ α*ε*‖g‖/(2 : ℝ)^23 := by
    change ‖(B : BrightSpace (SourceDecoration.Vertex S precision) →L[ℂ]
      BrightSpace (SourceDecoration.Vertex S precision)) _-_‖ ≤ _
    rw [hB]
    exact hr
  exact brightResponse_logical_budget (SourceIncidence.graph S precision) α
    (fun e => β (SourceIncidence.axis S precision e)) diag hα hε0 hε hK
    (fun e => hβlower (SourceIncidence.axis S precision e)) (SourceIncidence.degree_le_three S precision)
    B hnB herror _ g hrB

#print axioms idealSource_bright_residual
#print axioms source_bright_logical_residual

end Maxwell.Continuum.FiniteAuxiliary
