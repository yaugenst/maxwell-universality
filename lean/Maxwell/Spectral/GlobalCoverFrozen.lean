import Maxwell.Spectral.GlobalCover
import Maxwell.Certificate.GlobalScalar.Verified

/-! The fixed 2056-record scalar checks discharge every scalar and geometric
input of the global complement theorem. Only actual center trial bounds remain. -/
noncomputable section
namespace Maxwell.Spectral.GlobalCover
open Maxwell.Certificate Maxwell.Spectral.BoxNeighborhood

/-- Actual finite center matrices for the immutable comparator records. -/
def ComparatorCenters : Prop := ∀ i : Fin 2056,
  ∃ (low : Finset FourierBinding.Frequency)
      (Fn : NegativeCoordinates →L[ℂ] BoxMagnetic.Field)
      (Fp : PositiveCoordinates low →L[ℂ] BoxMagnetic.Field),
    CenterBounds GlobalComparison.comparatorMaterial (FrozenGlobal.center i) low
      (GlobalScalar.Frozen.constants i) Fn Fp

theorem comparator_certificates_of_centers (h : ComparatorCenters) : ComparatorBoxCertificates := by
  intro i
  obtain ⟨low, Fn, Fp, hF⟩ := h i
  exact ⟨GlobalScalar.Frozen.constants i, low, Fn, Fp,
    GlobalScalar.Frozen.accepted i, GlobalScalar.Frozen.constants_half i, rfl, hF⟩

theorem frozen_global_edge_gap (hn : NegativeCenters) (hp : ComparatorCenters)
    (c : PeriodicYee.Momentum) (hc : ¬ ReciprocalLocalBall c)
    (i : Fin (Module.finrank ℂ FourierBinding.FourierSpace)) :
    1/500000 ≤ |(FourierBinding.electricFiber_symmetric Concrete.material
      (FourierBinding.boundaryMomentum c)).eigenvalues rfl i-PointWitness.pointEnergy| :=
  global_edge_gap hn (comparator_certificates_of_centers hp) c hc i

theorem frozen_global_edge_invertible (hn : NegativeCenters) (hp : ComparatorCenters)
    (c : PeriodicYee.Momentum) (hc : ¬ ReciprocalLocalBall c) :
    (Matrix.toEuclideanCLM (n := PrimitiveYee.Electric) (𝕜 := ℂ)
      (PrimitiveYee.fiber Concrete.material (FourierBinding.boundaryMomentum c)) -
        (PointWitness.pointEnergy : ℂ) • 1).IsInvertible :=
  global_edge_invertible hn (comparator_certificates_of_centers hp) c hc

end Maxwell.Spectral.GlobalCover
