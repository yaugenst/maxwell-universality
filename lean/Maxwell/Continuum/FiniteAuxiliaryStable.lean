import Maxwell.Continuum.FiniteAuxiliaryBrightError
import Maxwell.Continuum.FiniteAuxiliaryInverse

/-! Stable assembly of the literal finite family of continuum wells.
Scalar spacing and certified tuning bounds imply invertibility of the
complete infinite-dimensional auxiliary operator. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048

namespace Maxwell.Continuum.FiniteAuxiliary

open Auxiliary EffectiveMass MasterConstants Maxwell.Composition

attribute [local irreducible] realMode Sh muH Cs

section Budget
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem exists_equiv_of_assembly_budget (T : E ≃L[ℂ] E) (A : E →L[ℂ] E)
    {K α ε δ : ℝ} (hK : 1 ≤ K) (hα : 0 < α) (hε : ε ≤ 1)
    (hT : ‖(T.symm : E →L[ℂ] E)‖ ≤ 16*K/α)
    (hA : ‖A-(T : E →L[ℂ] E)‖ ≤ δ)
    (hδ : δ ≤ α*ε/((2 : ℝ)^24*K)) :
    ∃ S : E ≃L[ℂ] E, (S : E →L[ℂ] E) = A ∧ ‖(S.symm : E →L[ℂ] E)‖ ≤ 32*K/α := by
  have hK0 : 0 < K := zero_lt_one.trans_le hK
  have hp : (16*K/α)*δ ≤ 1/2 := by
    calc
      (16*K/α)*δ ≤ (16*K/α)*(α*ε/((2 : ℝ)^24*K)) :=
        mul_le_mul_of_nonneg_left hδ (by positivity)
      _ = ε/(2 : ℝ)^20 := by field_simp; ring
      _ ≤ 1/2 := (div_le_div_of_nonneg_right hε (by positivity)).trans (by norm_num)
  obtain ⟨B, hB, hn⟩ := exists_equiv_of_half_error T A hT hA hp
  refine ⟨B, hB, hn.trans_eq ?_⟩
  ring

end Budget

variable (S : Source.SparseSystem) (precision : ℕ)
local instance : DecidableEq (SourceIncidence.V S precision) := Classical.decEq _

theorem exists_source_auxiliary_equiv {L d : ℕ} {z σ ε K α : ℝ}
    (hL : Ls ≤ (L : ℝ)) (D : Calibration (L : ℝ)⁻¹ z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ ((L : ℝ)⁻¹)^4/64) (hd : 1 ≤ d)
    (v : SourceDecoration.Vertex S precision → ℝ) (β : Fin 3 → ℝ)
    (diag : SourceIncidence.V S precision → ℝ)
    (hK : 1 ≤ K) (hα : 0 < α) (hα1 : α ≤ 1) (hε : ε ≤ 1)
    (hfirst : Cs^4*(L : ℝ)^12*((3 : ℝ)^d)⁻¹ ≤ ε/(2 : ℝ)^24)
    (hsecond : Cs^4*(L : ℝ)^12*(((3 : ℝ)^d)⁻¹)^2 ≤ α*ε/((2 : ℝ)^24*K))
    (hdiag : ∀ i, |(SourceIncidence.graph S precision).targetMatrix α
      (fun e => β (SourceIncidence.axis S precision e)) diag i i| ≤ (1/(2 : ℝ)^196)*(L : ℝ)^2)
    (hv : ∀ i, |(v i)⁻¹-(muH D (inverse_length_le_1024 hL)+
      (SourceIncidence.graph S precision).targetMatrix α
        (fun e => β (SourceIncidence.axis S precision e)) diag i i)| ≤ (((3 : ℝ)^d)⁻¹)^2)
    (hβ : ∀ j, |β j+usefulCoupling hL D d j| ≤ (((3 : ℝ)^d)⁻¹)^2/16)
    (htail : (Fintype.card (SourceDecoration.Vertex S precision) : ℝ)*Cs*(L : ℝ)^5*
      Real.exp (-cs*(L : ℝ)) ≤ (((3 : ℝ)^d)⁻¹)^2/4)
    (hdt : 16*σ*(L : ℝ)^4 ≤ (((3 : ℝ)^d)⁻¹)^2/(2 : ℝ)^20)
    (T : BrightSpace (SourceDecoration.Vertex S precision) ≃L[ℂ]
      BrightSpace (SourceDecoration.Vertex S precision))
    (hT : (T : BrightSpace (SourceDecoration.Vertex S precision) →L[ℂ]
      BrightSpace (SourceDecoration.Vertex S precision)) = logicalTarget (SourceIncidence.graph S precision) α
      (fun e => β (SourceIncidence.axis S precision e)) diag)
    (hTnorm : ‖(T.symm : BrightSpace (SourceDecoration.Vertex S precision) →L[ℂ]
      BrightSpace (SourceDecoration.Vertex S precision))‖ ≤ 16*K/α) :
    ∃ A : DefectSpace (SourceDecoration.Vertex S precision) ≃L[ℂ]
        DefectSpace (SourceDecoration.Vertex S precision),
      (A : DefectSpace (SourceDecoration.Vertex S precision) →L[ℂ]
        DefectSpace (SourceDecoration.Vertex S precision)) =
        auxiliaryMatrix D hσ0 hσ (centers L d (SourceDecoration.site S precision)) v ∧
      ‖(A.symm : DefectSpace (SourceDecoration.Vertex S precision) →L[ℂ]
        DefectSpace (SourceDecoration.Vertex S precision))‖ ≤ 256*K/α := by
  let p := SourceDecoration.site S precision
  let hh := inverse_length_le_1024 hL
  let M := auxiliaryMatrix D hσ0 hσ (centers L d p) v
  have hv' : ∀ i, |(v i)⁻¹-muH D hh| ≤ (1/(2 : ℝ)^196)*(L : ℝ)^2+(((3 : ℝ)^d)⁻¹)^2 := by
    intro i
    let θ := (SourceIncidence.graph S precision).targetMatrix α
      (fun e => β (SourceIncidence.axis S precision e)) diag i i
    calc
      |(v i)⁻¹-muH D hh| = |((v i)⁻¹-(muH D hh+θ))+θ| := congrArg abs (by ring)
      _ ≤ |(v i)⁻¹-(muH D hh+θ)|+|θ| := abs_add_le _ _
      _ ≤ (((3 : ℝ)^d)⁻¹)^2+(1/(2 : ℝ)^196)*(L : ℝ)^2 := add_le_add (hv i) (hdiag i)
      _ = _ := add_comm _ _
  have hM := assembly_complement_small hL D hh hσ0 hσ hd p
    (SourceDecoration.site_injective S precision) v hε hfirst hv' htail hdt
  have herr := source_reduced_error S precision hL D hσ0 hσ hd v α β diag hM hε hfirst hv hβ htail hdt
  rw [← hT] at herr
  obtain ⟨B, hB, hnB⟩ := exists_equiv_of_assembly_budget T (reducedMatrix D hh M hM)
    hK hα hε hTnorm herr hsecond
  let A := fullEquiv D hh M hM B hB
  refine ⟨A, fullEquiv_toContinuousLinearMap D hh M hM B hB, ?_⟩
  have hmix := (assembly_coupling_small hL D hσ0 hσ hd p
    (SourceDecoration.site_injective S precision) hε hfirst htail hdt).2
  have hnA := fullEquiv_inverse_norm D hh hσ0 hσ d p (SourceDecoration.site_injective S precision) v hM B hB hmix
  have hinv : (2 : ℝ)^193*((L : ℝ)⁻¹)^2 ≤ 1 := by
    calc
      (2 : ℝ)^193*((L : ℝ)⁻¹)^2 ≤ (2 : ℝ)^193*(1/(2 : ℝ)^1024)^2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (inv_nonneg.mpr (Nat.cast_nonneg L)) hh 2) (by positivity)
      _ ≤ 1 := by
        rw [div_pow, one_pow, mul_one_div]
        apply (div_le_one (by positivity : (0 : ℝ) < ((2 : ℝ)^1024)^2)).mpr
        rw [← pow_mul]
        exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
  have hKα : 1 ≤ K/α := (le_div_iff₀ hα).mpr (by simpa only [one_mul] using hα1.trans hK)
  apply hnA.trans
  have hb := add_le_add (mul_le_mul_of_nonneg_left hnB (by norm_num : (0 : ℝ) ≤ 4)) hinv
  apply hb.trans
  calc
    4*(32*K/α)+1 = 128*(K/α)+1 := by ring
    _ ≤ 256*(K/α) := by linarith only [hKα]
    _ = 256*K/α := by ring

#print axioms exists_source_auxiliary_equiv

end Maxwell.Continuum.FiniteAuxiliary
