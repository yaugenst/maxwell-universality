import Maxwell.Continuum.InvariantRestrictionDecomposition
import Maxwell.Continuum.Compression

/-! The bounded perturbation of an actual invariant-domain splitting is
exactly the low/high Schur block, under the ambient orthogonal unitary. -/

noncomputable section

namespace Maxwell.Continuum.InvariantRestriction.Data

open FormPerturbation

set_option backward.isDefEq.respectTransparency false

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {A : H →ₗ.[ℂ] H} {K : Submodule ℂ H} [CompleteSpace K]
variable (F : InvariantRestriction.Data A K) (hA : IsSelfAdjoint A)

/-- Actual lower-left compression of the bounded perturbation. -/
def coupling (B : H →L[ℂ] H) : K →L[ℂ] Kᗮ :=
  (Compression.offDiagonal K B).adjoint

/-- The actual high restriction, including the compressed perturbation. -/
def highBlock (B : H →L[ℂ] H) : Kᗮ →ₗ.[ℂ] Kᗮ :=
  addBounded (F.highOperator hA) (Compression.compress Kᗮ B)

theorem highBlock_selfAdjoint (B : H →L[ℂ] H) (hB : B.IsSymmetric) :
    IsSelfAdjoint (F.highBlock hA B) :=
  addBounded_selfAdjoint _ _ (F.high_selfAdjoint hA)
    (Compression.compress_symmetric Kᗮ B hB)

omit [CompleteSpace H] in
theorem bounded_low_decomposition (B : H →L[ℂ] H) (u : H) :
    K.orthogonalProjectionOnto (B u) =
      Compression.compress K B (K.orthogonalProjectionOnto u) +
        Compression.offDiagonal K B (Kᗮ.orthogonalProjectionOnto u) := by
  have h := congrArg (fun x => K.orthogonalProjectionOnto (B x)) (decomposition (K := K) u)
  simpa only [map_add, Compression.compress, Compression.offDiagonal,
    ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply] using h.symm

theorem bounded_high_decomposition (B : H →L[ℂ] H) (hB : B.IsSymmetric) (u : H) :
    Kᗮ.orthogonalProjectionOnto (B u) =
      coupling (K := K) B (K.orthogonalProjectionOnto u) +
        Compression.compress Kᗮ B (Kᗮ.orthogonalProjectionOnto u) := by
  rw [coupling, Compression.offDiagonal_adjoint K B hB]
  have h := congrArg (fun x => Kᗮ.orthogonalProjectionOnto (B x)) (decomposition (K := K) u)
  simpa only [map_add, Compression.compress,
    ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply] using h.symm

variable [FiniteDimensional ℂ K]

/-- The low block is the actual finite restriction plus the material compression. -/
def lowBlock (B : H →L[ℂ] H) : K →L[ℂ] K :=
  F.lowAction + Compression.compress K B

include hA in
theorem lowBlock_symmetric (B : H →L[ℂ] H) (hB : B.IsSymmetric) :
    (F.lowBlock B).IsSymmetric := by
  intro x y
  change inner ℂ (F.lowAction x + Compression.compress K B x) y =
    inner ℂ x (F.lowAction y + Compression.compress K B y)
  rw [inner_add_left, inner_add_right]
  exact congrArg₂ (· + ·) (F.lowAction_symmetric hA x y)
    (Compression.compress_symmetric K B hB x y)

/-- The literal partial block operator with domain K × D(A_high). -/
def blockOperator (B : H →L[ℂ] H) :
    HighSchur.Ambient K Kᗮ →ₗ.[ℂ] HighSchur.Ambient K Kᗮ :=
  HighSchur.block (F.lowBlock B) (coupling (K := K) B) (F.highBlock hA B)

/-- Exact operator intertwining, with the full domain equivalence. -/
theorem block_intertwine (B : H →L[ℂ] H) (hB : B.IsSymmetric) (u : A.domain) :
    K.orthogonalDecomposition (addBounded A B u) =
      F.blockOperator hA B (F.domainEquiv hA u) := by
  have hx : HighSchur.low (F.highBlock hA B) (F.domainEquiv hA u) =
      K.orthogonalProjectionOnto u := F.domainEquiv_low hA u
  have hy : HighSchur.high (F.highBlock hA B) (F.domainEquiv hA u) =
      F.domainHighProjection u := F.domainEquiv_high hA u
  change _ = HighSchur.block (F.lowBlock B) (coupling (K := K) B)
    (F.highBlock hA B) (F.domainEquiv hA u)
  rw [Submodule.orthogonalDecomposition_apply, HighSchur.block_apply, hx, hy]
  apply (WithLp.equiv 2 (K × Kᗮ)).injective
  apply Prod.ext
  · change K.orthogonalProjectionOnto (A u + B (u : H)) =
      (F.lowAction (K.orthogonalProjectionOnto u) +
        Compression.compress K B (K.orthogonalProjectionOnto u)) +
          (coupling (K := K) B).adjoint (F.domainHighProjection u)
    rw [map_add, F.lowProjection_action hA, bounded_low_decomposition,
      coupling, ContinuousLinearMap.adjoint_adjoint]
    change F.lowLinear (K.orthogonalProjectionOnto u) + (_ + _) =
      (F.lowLinear (K.orthogonalProjectionOnto u) + _) + _
    abel
  · change Kᗮ.orthogonalProjectionOnto (A u + B (u : H)) =
      coupling (K := K) B (K.orthogonalProjectionOnto u) +
        (F.highOperator hA (F.domainHighProjection u) +
          Compression.compress Kᗮ B (F.domainHighProjection u))
    rw [map_add, bounded_high_decomposition B hB, ← F.highProjection_action hA]
    abel

end Maxwell.Continuum.InvariantRestriction.Data
