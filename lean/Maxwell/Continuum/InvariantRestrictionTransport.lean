import Maxwell.Continuum.InvariantRestrictionBlock
import Maxwell.Continuum.HighSchurKernel

/-! Bounded inverses and kernel multiplicities are transported through the
literal orthogonal low/high decomposition of an unbounded operator. -/

noncomputable section

namespace Maxwell.Continuum.InvariantRestriction.Data

open FormPerturbation SelfAdjointResolvent

set_option backward.isDefEq.respectTransparency false

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {A : H →ₗ.[ℂ] H} {K : Submodule ℂ H} [CompleteSpace K]
variable [FiniteDimensional ℂ K]
variable (F : InvariantRestriction.Data A K) (hA : IsSelfAdjoint A)
variable (B : H →L[ℂ] H) (hB : B.IsSymmetric)

include hB

theorem block_intertwine_symm (v : (F.blockOperator hA B).domain) :
    addBounded A B ((F.domainEquiv hA).symm v) =
      K.orthogonalDecomposition.symm (F.blockOperator hA B v) := by
  apply K.orthogonalDecomposition.injective
  rw [F.block_intertwine hA B hB, LinearEquiv.apply_symm_apply,
    LinearIsometryEquiv.apply_symm_apply]

/-- A constructed product-block inverse gives a genuine inverse on the
original Hilbert space, with its actual domain and both inverse laws. -/
def inverseFromBlock (Q : BoundedInverse (F.blockOperator hA B)) :
    BoundedInverse (addBounded A B) where
  map := K.orthogonalDecomposition.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (Q.map.comp K.orthogonalDecomposition.toContinuousLinearEquiv.toContinuousLinearMap)
  mem_domain f := (F.product_mem_domain_iff hA _).mp (Q.mem_domain _)
  apply_map f := by
    let q : (F.blockOperator hA B).domain :=
      ⟨Q.map (K.orthogonalDecomposition f), Q.mem_domain _⟩
    change addBounded A B ((F.domainEquiv hA).symm q) = f
    rw [F.block_intertwine_symm hA B hB, Q.apply_map]
    exact K.orthogonalDecomposition.symm_apply_apply f
  map_apply u := by
    change K.orthogonalDecomposition.symm
      (Q.map (K.orthogonalDecomposition (addBounded A B u))) = (u : H)
    rw [F.block_intertwine hA B hB, Q.map_apply, F.domainEquiv_coe]
    exact K.orthogonalDecomposition.symm_apply_apply u

/-- Conversely, an actual ambient inverse gives the product-block inverse. -/
def inverseToBlock (R : BoundedInverse (addBounded A B)) :
    BoundedInverse (F.blockOperator hA B) where
  map := K.orthogonalDecomposition.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (R.map.comp K.orthogonalDecomposition.symm.toContinuousLinearEquiv.toContinuousLinearMap)
  mem_domain f := by
    apply (F.product_mem_domain_iff hA _).mpr
    change K.orthogonalDecomposition.symm
      (K.orthogonalDecomposition (R.map (K.orthogonalDecomposition.symm f))) ∈ A.domain
    simpa only [LinearIsometryEquiv.symm_apply_apply, addBounded_domain] using
      R.mem_domain (K.orthogonalDecomposition.symm f)
  apply_map f := by
    let r : A.domain := ⟨R.map (K.orthogonalDecomposition.symm f), R.mem_domain _⟩
    change F.blockOperator hA B (F.domainEquiv hA r) = f
    rw [← F.block_intertwine hA B hB, R.apply_map]
    exact K.orthogonalDecomposition.apply_symm_apply f
  map_apply v := by
    change K.orthogonalDecomposition
      (R.map (K.orthogonalDecomposition.symm (F.blockOperator hA B v))) =
        (v : HighSchur.Ambient K Kᗮ)
    rw [← F.block_intertwine_symm hA B hB, R.map_apply, F.domainEquiv_symm_coe]
    exact K.orthogonalDecomposition.apply_symm_apply v

theorem inverse_iff_block_inverse :
    Nonempty (BoundedInverse (addBounded A B)) ↔
      Nonempty (BoundedInverse (F.blockOperator hA B)) :=
  ⟨fun ⟨R⟩ => ⟨F.inverseToBlock hA B hB R⟩,
    fun ⟨Q⟩ => ⟨F.inverseFromBlock hA B hB Q⟩⟩

theorem mem_ker_iff_block (x : H) :
    x ∈ (addBounded A B).ker ↔
      K.orthogonalDecomposition x ∈ (F.blockOperator hA B).ker := by
  constructor
  · intro hx
    let u : A.domain := ⟨x, (addBounded A B).ker_le_domain hx⟩
    apply (LinearPMap.coe_mem_ker_iff
      (f := F.blockOperator hA B) (x := F.domainEquiv hA u)).mpr
    rw [← F.block_intertwine hA B hB]
    have hz : addBounded A B u = 0 := LinearPMap.coe_mem_ker_iff.mp hx
    rw [hz, map_zero]
  · intro hx
    have hd : K.orthogonalDecomposition x ∈ (F.blockOperator hA B).domain :=
      (F.blockOperator hA B).ker_le_domain hx
    have hm := (F.product_mem_domain_iff hA _).mp hd
    rw [LinearIsometryEquiv.symm_apply_apply] at hm
    let u : A.domain := ⟨x, hm⟩
    apply (LinearPMap.coe_mem_ker_iff (f := addBounded A B) (x := u)).mpr
    apply K.orthogonalDecomposition.injective
    rw [map_zero, F.block_intertwine hA B hB]
    exact LinearPMap.coe_mem_ker_iff.mp hx

def kernelToBlock : (addBounded A B).ker →ₗ[ℂ] (F.blockOperator hA B).ker :=
  (K.orthogonalDecomposition.toLinearMap.comp (addBounded A B).ker.subtype).codRestrict
    (F.blockOperator hA B).ker (fun x => (F.mem_ker_iff_block hA B hB x).mp x.property)

def kernelFromBlock : (F.blockOperator hA B).ker →ₗ[ℂ] (addBounded A B).ker :=
  (K.orthogonalDecomposition.symm.toLinearMap.comp
    (F.blockOperator hA B).ker.subtype).codRestrict (addBounded A B).ker (by
      intro y
      apply (F.mem_ker_iff_block hA B hB _).mpr
      change K.orthogonalDecomposition (K.orthogonalDecomposition.symm y) ∈ _
      simpa only [LinearIsometryEquiv.apply_symm_apply] using y.property)

/-- The actual ambient kernel has precisely the block kernel multiplicity. -/
def kernelBlockEquiv : (addBounded A B).ker ≃ₗ[ℂ] (F.blockOperator hA B).ker where
  __ := F.kernelToBlock hA B hB
  invFun := F.kernelFromBlock hA B hB
  left_inv x := Subtype.ext (K.orthogonalDecomposition.symm_apply_apply x)
  right_inv y := Subtype.ext (K.orthogonalDecomposition.apply_symm_apply y)

/-- Combining the ambient unitary with high-block elimination preserves all
kernel multiplicities, including repeated eigenvalues. -/
def kernelSchurEquiv (R : BoundedInverse (F.highBlock hA B)) :
    (addBounded A B).ker ≃ₗ[ℂ]
      (HighSchur.schur (F.lowBlock B) (coupling (K := K) B) R).ker :=
  (F.kernelBlockEquiv hA B hB).trans
    (HighSchur.kernelEquiv (F.lowBlock B) (coupling (K := K) B) R)

theorem kernel_schur_finrank (R : BoundedInverse (F.highBlock hA B)) :
    Module.finrank ℂ (addBounded A B).ker =
      Module.finrank ℂ (HighSchur.schur (F.lowBlock B) (coupling (K := K) B) R).ker :=
  (F.kernelSchurEquiv hA B hB R).finrank_eq

/-- Nonvanishing of the finite Schur operator constructs an actual full
resolvent; it does not merely exclude eigenvectors. -/
theorem inverse_iff_schur_ker_eq_bot (R : BoundedInverse (F.highBlock hA B)) :
    Nonempty (BoundedInverse (addBounded A B)) ↔
      (HighSchur.schur (F.lowBlock B) (coupling (K := K) B) R).ker = ⊥ := by
  rw [F.inverse_iff_block_inverse hA B hB]
  exact HighSchur.block_inverse_iff_schur_ker_eq_bot _ _ R

end Maxwell.Continuum.InvariantRestriction.Data
