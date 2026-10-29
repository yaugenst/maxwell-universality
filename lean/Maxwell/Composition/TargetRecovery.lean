import Maxwell.Composition.Recovery
import Maxwell.Composition.Complex
import Maxwell.TargetAccess

/-! The finite physical composition applied to the actual emitted target
matrix, source, tolerance, and every admissible complex solver output.
The explicit local decomposition hypotheses must still be instantiated by
the physical construction; they are not axioms or a presumed final theorem. -/

noncomputable section

namespace Maxwell.Composition

def targetRealSource {n : ℕ} (I : Target.Instance n) : EuclideanSpace ℝ I.box.Edge :=
  WithLp.toLp 2 fun e => (I.source e : ℝ)

/-- The real part of every admissible complex field lies in the same
polynomial amplitude ball when the full emitted real operator is invertible.
This bounds exactly the coordinates queried by the finite decoder. -/
theorem target_admissible_amplitude {n : ℕ} (I : Target.Instance n)
    (A : EuclideanSpace ℝ I.box.Edge ≃L[ℝ] EuclideanSpace ℝ I.box.Edge)
    (hA : (A : EuclideanSpace ℝ I.box.Edge →L[ℝ] EuclideanSpace ℝ I.box.Edge) =
      I.realOperator)
    (Q F : ℝ) (hInv : ‖(A.symm : EuclideanSpace ℝ I.box.Edge →L[ℝ]
      EuclideanSpace ℝ I.box.Edge)‖ ≤ Q)
    (hF : ‖targetRealSource I‖ ≤ F) (hδ : (I.tolerance : ℝ) ≤ 1 / 2)
    (y : EuclideanSpace ℂ I.box.Edge) (hy : I.Admissible y) :
    ‖euclideanRealPart y‖ ≤ 3 * Q * F / 2 := by
  have hres : ‖A (euclideanRealPart y) - targetRealSource I‖ ≤ F / 2 := by
    change ‖(A : EuclideanSpace ℝ I.box.Edge →L[ℝ] EuclideanSpace ℝ I.box.Edge)
      (euclideanRealPart y) - targetRealSource I‖ ≤ F / 2
    rw [hA]
    calc
      _ ≤ (I.tolerance : ℝ) * ‖targetRealSource I‖ :=
        target_admissible_real_residual I y hy
      _ ≤ (1 / 2) * ‖targetRealSource I‖ :=
        mul_le_mul_of_nonneg_right hδ (norm_nonneg _)
      _ ≤ (1 / 2) * F := mul_le_mul_of_nonneg_left hF (by norm_num)
      _ = F / 2 := by ring
  calc
    _ ≤ Q * (F + F / 2) :=
      amplitude_of_residual A _ (targetRealSource I) Q F (F / 2) hInv hF hres
    _ = 3 * Q * F / 2 := by ring

theorem weightedDecoder_fits_of_amplitude {ι : Type*} [Fintype ι] {n : ℕ}
    (D : Target.WeightedDecoder ι n) (y : EuclideanSpace ℝ ι)
    (B : ℝ) (hB : ‖y‖ ≤ B) (hrange : B < (2 : ℝ) ^ D.format.integerBits) :
    D.Fits y := by
  intro j
  have hcoord : |y (D.coordinate j)| ≤ B := by
    exact (PiLp.norm_apply_le y (D.coordinate j)).trans hB
  have h := abs_lt.mp (hcoord.trans_lt hrange)
  exact ⟨h.1.le, h.2⟩

/-- The same full-inverse bound supplies nonvacuous fixed-width access for
every admissible complex output. No output-dependent exception or width
extension is introduced. -/
theorem target_admissible_finite_access {n : ℕ} (I : Target.Instance n)
    (A : EuclideanSpace ℝ I.box.Edge ≃L[ℝ] EuclideanSpace ℝ I.box.Edge)
    (hA : (A : EuclideanSpace ℝ I.box.Edge →L[ℝ] EuclideanSpace ℝ I.box.Edge) =
      I.realOperator)
    (Q F : ℝ) (hInv : ‖(A.symm : EuclideanSpace ℝ I.box.Edge →L[ℝ]
      EuclideanSpace ℝ I.box.Edge)‖ ≤ Q)
    (hF : ‖targetRealSource I‖ ≤ F) (hδ : (I.tolerance : ℝ) ≤ 1 / 2)
    (hrange : 3 * Q * F / 2 < (2 : ℝ) ^ I.decoder.format.integerBits)
    (y : EuclideanSpace ℂ I.box.Edge) (hy : I.Admissible y) :
    I.decoder.Fits (fun e => (y e).re) ∧
      ∃ w : I.decoder.Messages, I.decoder.Accurate w (fun e => (y e).re) := by
  have hfit : I.decoder.Fits (fun e => (y e).re) :=
    weightedDecoder_fits_of_amplitude I.decoder (euclideanRealPart y) (3 * Q * F / 2)
      (target_admissible_amplitude I A hA Q F hInv hF hδ y hy) hrange
  exact ⟨hfit, I.decoder.exists_accurate_messages _ hfit⟩

section ActualBrightRecovery

variable {D B C : Type*}
variable [NormedAddCommGroup D] [NormedSpace ℝ D]
variable [NormedAddCommGroup B] [NormedSpace ℝ B]
variable [NormedAddCommGroup C] [NormedSpace ℝ C]

/-- Actual-target specialization of the source-to-bright residual theorem.
All complex outputs satisfying the one emitted tolerance obey this bound;
the event needed for its local operator premises is independent of the output. -/
theorem target_admissible_bright_residual_budget {n : ℕ} (I : Target.Instance n)
    (K : EuclideanSpace ℝ I.box.Edge ≃L[ℝ] EuclideanSpace ℝ I.box.Edge)
    (V W : D ≃L[ℝ] D)
    (Q : EuclideanSpace ℝ I.box.Edge →L[ℝ] D)
    (Qt : D →L[ℝ] EuclideanSpace ℝ I.box.Edge)
    (U : B →L[ℝ] D) (Z : C →L[ℝ] D)
    (P : D →L[ℝ] B) (R : D →L[ℝ] C) (Dc : C ≃L[ℝ] C)
    (hphysical : I.realOperator = finitePhysicalOperator K V Q Qt)
    (hQQt : ∀ d, Q (Qt d) = d)
    (hdecomp : ∀ d, d = U (P d) + Z (R d))
    (hDc : ∀ c, R (weightedBirmanSchwinger K V W Q Qt (Z c)) = Dc c)
    (hPU : ∀ b, P (U b) = b) (hRU : ∀ b, R (U b) = 0)
    (α ε G J cW L : ℝ) (hε : 0 ≤ ε)
    (hJ : 0 < J) (hcW : 0 < cW) (hL : 0 < L)
    (hK : ‖(K.symm : EuclideanSpace ℝ I.box.Edge →L[ℝ]
      EuclideanSpace ℝ I.box.Edge)‖ ≤ L)
    (hW : ‖(W : D →L[ℝ] D)‖ ≤ 1) (hQ : ‖Q‖ ≤ 1)
    (hP : ‖P‖ ≤ 1) (hR : ‖R‖ ≤ 1)
    (hmix : ‖(P.comp ((weightedBirmanSchwinger K V W Q Qt).comp Z)).comp
      (Dc.symm : C →L[ℝ] C)‖ ≤ 1)
    (g : B)
    (hsourceNorm : ‖targetRealSource I‖ ≤ 2 * α * J * cW * G)
    (hsourceError : ‖targetRealSource I - localIdealSource K W Qt (U (α • g))‖ ≤
      α * ε * G / (8192 * L))
    (htolerance : (I.tolerance : ℝ) ≤ ε / (8192 * J * cW * L))
    (y : EuclideanSpace ℂ I.box.Edge) (hy : I.Admissible y) :
    ‖brightSchurOperator (weightedBirmanSchwinger K V W Q Qt) U Z P R Dc
      (P (weightedDefectCoordinates V W Q (euclideanRealPart y))) - α • g‖ ≤
        3 * α * ε * G / 4096 := by
  have hsolver : ‖finitePhysicalOperator K V Q Qt (euclideanRealPart y) -
      targetRealSource I‖ ≤
      (ε / (8192 * J * cW * L)) * ‖targetRealSource I‖ := by
    rw [← hphysical]
    exact (target_admissible_real_residual I y hy).trans
      (mul_le_mul_of_nonneg_right htolerance (norm_nonneg _))
  exact physical_bright_residual_budget K V W Q Qt U Z P R Dc hQQt hdecomp
    hDc hPU hRU α ε G J cW L hε hJ hcW hL hK hW hQ hP hR hmix g
    (euclideanRealPart y) (targetRealSource I) hsourceNorm hsourceError hsolver

end ActualBrightRecovery

end Maxwell.Composition
