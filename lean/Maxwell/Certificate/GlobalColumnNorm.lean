import Maxwell.Certificate.DyadicKernelGramSound
import Maxwell.Certificate.FourierBinding

/-! Axis-major checker rows are exactly the actual primitive electric field
coordinates. The coordinate change is an isometry, so Gram acceptance loses
no dimension factor when transferred to the physical synthesis map. -/
namespace Maxwell.Certificate.GlobalColumnNorm
open Maxwell.Spectral.PrimitiveYee FourierBinding ComplexNormCertificate

def cellIndex : Cell ≃ Fin 2000 :=
  (Equiv.prodCongr (Equiv.refl (Fin 20))
    (finProdFinEquiv : Fin 10 × Fin 10 ≃ Fin 100)).trans finProdFinEquiv

def electricIndex : Electric ≃ Fin 6000 :=
  (Equiv.prodCongr (Equiv.refl (Fin 3)) cellIndex).trans finProdFinEquiv

theorem electricIndex_val (e : Electric) :
    (electricIndex e).val = 2000*e.1.val+100*e.2.1.val+10*e.2.2.1.val+e.2.2.2.val := by
  change e.2.2.2.val+10*e.2.2.1.val+100*e.2.1.val+2000*e.1.val = _
  omega

noncomputable section

def coordinates : FourierSpace ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin 6000) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ electricIndex

theorem coordinates_apply (v : FourierSpace) (i : Fin 6000) :
    coordinates v i = v (electricIndex.symm i) := rfl

variable {n : ℕ}

def fieldMatrix (v : Fin n → FourierSpace) : Matrix Electric (Fin n) ℂ := columnsMatrix v

def fieldSynthesis (v : Fin n → FourierSpace) : EuclideanSpace ℂ (Fin n) →L[ℂ] FourierSpace :=
  rectangularOperator (fieldMatrix v)

def flatMatrix (v : Fin n → FourierSpace) : Matrix (Fin 6000) (Fin n) ℂ :=
  fun i j => v j (electricIndex.symm i)

theorem fieldSynthesis_apply (v : Fin n → FourierSpace) (x : EuclideanSpace ℂ (Fin n)) :
    fieldSynthesis v x = ∑ j, x j • v j := rectangularOperator_columns_apply v x

theorem flatOperator_binding (v : Fin n → FourierSpace) :
    rectangularOperator (flatMatrix v) = coordinates.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (fieldSynthesis v) := by
  apply ContinuousLinearMap.ext
  intro x
  change rectangularOperator (columnsMatrix (fun j => coordinates (v j))) x =
    coordinates (fieldSynthesis v x)
  rw [rectangularOperator_columns_apply,fieldSynthesis_apply,map_sum]
  simp only [map_smul]

theorem flatOperator_norm (v : Fin n → FourierSpace) :
    ‖rectangularOperator (flatMatrix v)‖ = ‖fieldSynthesis v‖ := by
  rw [flatOperator_binding]
  exact coordinates.toLinearIsometry.norm_toContinuousLinearMap_comp

/-- A computed Gram/Schur acceptance controls the actual Fourier-space
column synthesis, with only input containment and the checked scalar bound. -/
theorem gramNormEval_sound {p r : ℕ} {boundSquared : DyadicKernel.Rectangle}
    {a : DyadicKernel.Rectangular 6000 n} (v : Fin n → FourierSpace) {C : ℝ}
    (h : DyadicKernel.gramNormEval p r boundSquared a = true) (hC : 0 ≤ C)
    (hb : boundSquared.toDyadic.Contains p (((2:ℝ)^r)⁻¹*C^2:ℝ))
    (ha : ∀ i j, (a.entry i j).toDyadic.Contains p (v j (electricIndex.symm i))) :
    ‖fieldSynthesis v‖ ≤ C := by
  rw [← flatOperator_norm]
  exact DyadicKernel.gramNormEval_sound h hC hb ha

/-- The same checked bound applies to any already constructed map with these
actual columns; no new choice of trial vectors is introduced. -/
theorem gramNormEval_map {p r : ℕ} {boundSquared : DyadicKernel.Rectangle}
    {a : DyadicKernel.Rectangular 6000 n} (F : EuclideanSpace ℂ (Fin n) →L[ℂ] FourierSpace)
    {C : ℝ} (h : DyadicKernel.gramNormEval p r boundSquared a = true) (hC : 0 ≤ C)
    (hb : boundSquared.toDyadic.Contains p (((2:ℝ)^r)⁻¹*C^2:ℝ))
    (ha : ∀ i j, (a.entry i j).toDyadic.Contains p
      (F (EuclideanSpace.basisFun (Fin n) ℂ j) (electricIndex.symm i))) : ‖F‖ ≤ C := by
  have he : fieldSynthesis (fun j => F (EuclideanSpace.basisFun (Fin n) ℂ j))=F := by
    apply ContinuousLinearMap.ext
    intro x
    rw [fieldSynthesis_apply]
    calc
      ∑ j, x j • F (EuclideanSpace.basisFun (Fin n) ℂ j) =
          F (∑ j, x j • EuclideanSpace.basisFun (Fin n) ℂ j) := by
        simp only [map_sum,map_smul]
      _ = F x := by
        congr 1
        exact (EuclideanSpace.basisFun (Fin n) ℂ).sum_repr x
  rw [← he]
  exact gramNormEval_sound _ h hC hb ha

end
end Maxwell.Certificate.GlobalColumnNorm
