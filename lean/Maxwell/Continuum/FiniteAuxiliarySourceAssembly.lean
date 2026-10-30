import Maxwell.Continuum.FiniteAuxiliaryBrightRecovery
import Maxwell.Continuum.FiniteAuxiliarySourceTarget
import Maxwell.Continuum.FiniteAuxiliaryReadout

/-! Actual finite continuum assembly and ideal observable recovery.
The inverse and all logical residual estimates are constructed from
the sparse-source promise and the finite tuning/spacing tests. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048
set_option maxHeartbeats 800000

namespace Maxwell.Continuum.FiniteAuxiliary

open Auxiliary EffectiveMass MasterConstants Maxwell.Composition

attribute [local irreducible] Auxiliary.resolvent realMode Sh muH Qh Cs

variable (S : Source.SparseSystem) (precision : ℕ)
local instance sourceAssemblyDecidableEq : DecidableEq (SourceIncidence.V S precision) := Classical.decEq _

theorem exists_routed_response
    (hunit : IsUnit (Source.realMatrix S)) (hm : 2 ≤ S.nnz) (hp : 1 ≤ precision)
    (hsmall : ((S.nnz : ℝ)*Maxwell.condition₂ (Source.realMatrix S))*
      ((S.nnz : ℝ)/(2*2^precision)) ≤ 1/2)
    {κ K α ε : ℝ} (hκ : 1 ≤ κ) (hα : 0 < α) (hα1 : α ≤ 1) (hK : 1 ≤ K)
    (hcondition : (S.nnz : ℝ)*Maxwell.condition₂ (Source.realMatrix S) ≤ κ)
    (hbudget : SourceMediator.inverseBudget S precision κ ≤ K)
    {L d : ℕ} {z σ : ℝ} (hL : Ls ≤ (L : ℝ)) (D : Calibration (L : ℝ)⁻¹ z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ ((L : ℝ)⁻¹)^4/64) (hd : 1 ≤ d)
    (v : SourceDecoration.Vertex S precision → ℝ) (hvpos : ∀ i, 0 < v i) (β : Fin 3 → ℝ)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1)
    (hfirst : Cs^4*(L : ℝ)^12*((3 : ℝ)^d)⁻¹ ≤ ε/(2 : ℝ)^24)
    (hsecond : Cs^4*(L : ℝ)^12*(((3 : ℝ)^d)⁻¹)^2 ≤ α*ε/((2 : ℝ)^24*K))
    (hdiag : ∀ i, |(SourceIncidence.graph S precision).targetMatrix α
      (fun e => β (SourceIncidence.axis S precision e)) (SourceMediator.diagonal S precision) i i| ≤
        (1/(2 : ℝ)^196)*(L : ℝ)^2)
    (hv : ∀ i, |(v i)⁻¹-(muH D (inverse_length_le_1024 hL)+
      (SourceIncidence.graph S precision).targetMatrix α
        (fun e => β (SourceIncidence.axis S precision e)) (SourceMediator.diagonal S precision) i i)| ≤
          (((3 : ℝ)^d)⁻¹)^2)
    (hβ : ∀ j, |β j+usefulCoupling hL D d j| ≤ (((3 : ℝ)^d)⁻¹)^2/16)
    (hβlower : ∀ j, 3*α ≤ |β j|)
    (htail : (Fintype.card (SourceDecoration.Vertex S precision) : ℝ)*Cs*(L : ℝ)^5*
      Real.exp (-cs*(L : ℝ)) ≤ (((3 : ℝ)^d)⁻¹)^2/4)
    (hdt : 16*σ*(L : ℝ)^4 ≤ (((3 : ℝ)^d)⁻¹)^2/(2 : ℝ)^20) :
    ∃ A : DefectSpace (SourceDecoration.Vertex S precision) ≃L[ℂ]
        DefectSpace (SourceDecoration.Vertex S precision),
      (A : DefectSpace (SourceDecoration.Vertex S precision) →L[ℂ]
        DefectSpace (SourceDecoration.Vertex S precision)) =
        auxiliaryMatrix D hσ0 hσ (centers L d (SourceDecoration.site S precision)) v ∧
      ‖(A.symm : DefectSpace (SourceDecoration.Vertex S precision) →L[ℂ]
        DefectSpace (SourceDecoration.Vertex S precision))‖ ≤ 256*K/α ∧
      ∀ g : EuclideanSpace ℂ (SourceIncidence.V S precision),
        ‖ComplexInverse.complexOperator
          ((SourceIncidence.graph S precision).logicalMatrix (SourceMediator.diagonal S precision))
          (complexTerminalPart (idealReadout (L : ℝ)⁻¹ (centers L d (SourceDecoration.site S precision)) v
            (realMode D (inverse_length_le_1024 hL))
            (auxiliaryField D hσ0 hσ (centers L d (SourceDecoration.site S precision)) A
              (idealSource D (inverse_length_le_1024 hL) (centers L d (SourceDecoration.site S precision)) α
                (complexTerminalInjection g)))))-g‖ ≤ ε*‖g‖/1024 := by
  obtain ⟨T, hT, hnT⟩ := exists_routed_target_equiv S precision hunit hm hp hsmall κ K α
    hκ hα hcondition hbudget β hβlower
  obtain ⟨A, hA, hnA⟩ := exists_source_auxiliary_equiv S precision hL D hσ0 hσ hd v β
    (SourceMediator.diagonal S precision) hK hα hα1 hε hfirst hsecond hdiag hv hβ htail hdt T hT hnT
  refine ⟨A, hA, hnA, ?_⟩
  have hv' : ∀ i, |(v i)⁻¹-muH D (inverse_length_le_1024 hL)| ≤
      (1/(2 : ℝ)^196)*(L : ℝ)^2+(((3 : ℝ)^d)⁻¹)^2 := by
    intro i
    let θ := (SourceIncidence.graph S precision).targetMatrix α
      (fun e => β (SourceIncidence.axis S precision e)) (SourceMediator.diagonal S precision) i i
    calc
      _ = |((v i)⁻¹-(muH D (inverse_length_le_1024 hL)+θ))+θ| := congrArg abs (by ring)
      _ ≤ |(v i)⁻¹-(muH D (inverse_length_le_1024 hL)+θ)|+|θ| := abs_add_le _ _
      _ ≤ (((3 : ℝ)^d)⁻¹)^2+(1/(2 : ℝ)^196)*(L : ℝ)^2 := add_le_add (hv i) (hdiag i)
      _ = _ := add_comm _ _
  have hM := assembly_complement_small hL D (inverse_length_le_1024 hL) hσ0 hσ hd
    (SourceDecoration.site S precision) (SourceDecoration.site_injective S precision) v hε hfirst hv' htail hdt
  intro g
  rw [idealReadout_auxiliaryField D (inverse_length_le_1024 hL) hσ0 hσ _ v
    (fun i => (hvpos i).ne') A hA]
  exact source_bright_logical_residual S precision hL D hσ0 hσ hd v β
    (SourceMediator.diagonal S precision) hK hα hε0 hε hfirst hsecond hv hβ hβlower htail hdt
    hM A hA T hT hnT g

#print axioms exists_routed_response

end Maxwell.Continuum.FiniteAuxiliary
