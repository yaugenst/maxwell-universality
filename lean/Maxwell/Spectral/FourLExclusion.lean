import Maxwell.Spectral.FourLGeometry
import Maxwell.Spectral.CenteredInverse
import Maxwell.Spectral.GlobalCoverFrozen

namespace Maxwell.Spectral.FourLGeometry
open Maxwell.Certificate.FourierBinding
open PeriodicYee (Momentum)
open PrimitiveYee ReciprocalCover GlobalCover LocalClusterCount YeeTaylorRemainder
noncomputable section

/-- The selected primitive center, modulo its actual reciprocal lattice. -/
def SelectedClass (c : Momentum) : Prop := ∃ n : Translation, c=center 0+reciprocalShift n

theorem local_invertible (E : ℝ)
    (hcenter : ∀ a : Fin 4, a ≠ 0 →
      (Matrix.toEuclideanCLM (n := Electric) (𝕜 := ℂ)
        (fiber Concrete.material (boundaryMomentum (center a))) - (E:ℂ) • 1).IsInvertible)
    (hpuncture : ∀ (a : Fin 4) (q : Momentum), 0 < YeeTaylor.radius q →
      YeeTaylor.radius q ≤ 1/20 → (centeredOperator (point a) q-(E:ℂ) • 1).IsInvertible)
    (c : Momentum) (hc : ReciprocalLocalBall c) (hselected : ¬ SelectedClass c) :
    (Matrix.toEuclideanCLM (n := Electric) (𝕜 := ℂ)
      (fiber Concrete.material (boundaryMomentum c))-(E:ℂ) • 1).IsInvertible := by
  obtain ⟨a,n,q,rfl,hq⟩ := reciprocal_local_decomposition c hc
  rw [fiber_reciprocal_periodic]
  by_cases hzero : q=0
  · subst q
    have ha : a ≠ 0 := by
      intro he
      subst a
      apply hselected
      exact ⟨n,by simp [centeredMomentum,center]⟩
    simpa only [centeredMomentum,add_zero,center] using hcenter a ha
  · have hr : 0 < YeeTaylor.radius q := by
      apply norm_pos_iff.mpr
      intro hh
      apply hzero
      exact (WithLp.toLp_injective 2).eq_iff.mp hh
    exact CenteredInverse.boundary_of_centered (point a) q E (hpuncture a q hr hq)

/-- Combining the actual finite-cover inverse with the four local proofs
removes every primitive momentum except the selected reciprocal class. -/
theorem primitive_edge_invertible (hn : NegativeCenters) (hp : ComparatorCenters)
    (hcenter : ∀ a : Fin 4, a ≠ 0 →
      (Matrix.toEuclideanCLM (n := Electric) (𝕜 := ℂ)
        (fiber Concrete.material (boundaryMomentum (center a))) -
          (Maxwell.Certificate.PointWitness.pointEnergy:ℂ) • 1).IsInvertible)
    (hpuncture : ∀ (a : Fin 4) (q : Momentum), 0 < YeeTaylor.radius q →
      YeeTaylor.radius q ≤ 1/20 → (centeredOperator (point a) q-
        (Maxwell.Certificate.PointWitness.pointEnergy:ℂ) • 1).IsInvertible)
    (c : Momentum) (hselected : ¬ SelectedClass c) :
    (Matrix.toEuclideanCLM (n := Electric) (𝕜 := ℂ)
      (fiber Concrete.material (boundaryMomentum c))-
        (Maxwell.Certificate.PointWitness.pointEnergy:ℂ) • 1).IsInvertible := by
  by_cases hc : ReciprocalLocalBall c
  · exact local_invertible _ hcenter hpuncture c hc hselected
  · exact frozen_global_edge_invertible hn hp c hc

end
end Maxwell.Spectral.FourLGeometry
