import Maxwell.Certificate.UniformLocalScalar.Verified
import Maxwell.Spectral.LocalClusterCount
import Maxwell.Spectral.GlobalCover

/-! The single uniform local-count matrix certificate controls every signed
L neighborhood. Cubic symmetry is used only for the unperturbed, uniformly
shifted material; perturbation order transfers the count to the frozen material. -/
noncomputable section
namespace Maxwell.Spectral.UniformLocalNeighborhood

open Maxwell.Certificate Maxwell.Certificate.FourierBinding
open Maxwell.Spectral.PeriodicYee (Momentum Cell20)
open Maxwell.Spectral.PrimitiveYee LocalClusterCount GlobalCover ReciprocalCover

def center : Momentum := fun _ => 1/2
abbrev bounds := UniformLocalScalar.Frozen.constants

/-- The remaining finite input consists solely of actual center-matrix
inequalities for the four negative and `2*low.card-4` positive columns. -/
def CenterCertificate : Prop := ∃ (low : Finset Frequency)
    (Fn : BoxNeighborhoodGeneral.NegativeCoordinates 4 →L[ℂ] BoxMagnetic.Field)
    (Fp : BoxNeighborhoodGeneral.PositiveCoordinates 4 low →L[ℂ] BoxMagnetic.Field),
  BoxNeighborhoodGeneral.CenterBounds localMaterial center low 4 bounds Fn Fp

theorem upper_count_at_positive_center (hc : CenterCertificate)
    (q : Momentum) (hq : YeeTaylor.radius q ≤ 1/20) :
    electricCount localMaterial (center+q) (1/4096) ≤ 2004 := by
  obtain ⟨low, Fn, Fp, hcenter⟩ := hc
  have hm (e : Electric) : 1 ≤ edgeAverage localMaterial e ∧ edgeAverage localMaterial e ≤ bounds.rho := by
    simpa only [UniformLocalScalar.Frozen.rho_eq] using localMaterial_edge_bounds e
  have hbox := UniformLocalScalar.Frozen.ball_subset_box q hq
  have hshift : |(1/64+1/4096 : ℝ)-1/64| ≤ bounds.σ := by
    rw [UniformLocalScalar.Frozen.sigma_eq]
    norm_num
  have hmag := BoxNeighborhoodGeneral.accepted_box_magnetic_count
    UniformLocalScalar.Frozen.accepted hcenter hm q (1/64+1/4096) hbox hshift
  exact (MagneticThreshold.energy_threshold_upper localMaterial
    (fun e => (localMaterial_edge_bounds e).1) (center+q) (1/4096) (by norm_num)).trans hmag.le

theorem abs_displacement_radius (v : Momentum) (hv : SignedLocalBall v) :
    YeeTaylor.radius (fun j => |v j|-1/2) ≤ 1/20 := by
  obtain ⟨s, hs, hsq⟩ := hv
  have hj (j : PeriodicYee.Direction) : (|v j|-1/2)^2 ≤ (v j-(s j : ℝ)/2)^2 := by
    rcases hs j with h | h
    · rw [h]
      norm_num
      rcases le_total 0 (v j) with hv | hv
      · rw [abs_of_nonneg hv]
      · rw [abs_of_nonpos hv]
        nlinarith
    · rw [h]
      norm_num
      rcases le_total 0 (v j) with hv | hv
      · rw [abs_of_nonneg hv]
        nlinarith
      · rw [abs_of_nonpos hv]
        ring_nf
        rfl
  have hsum := (Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hj j)).trans hsq
  rw [← YeeTaylor.radius_sq] at hsum
  have hn : 0 ≤ YeeTaylor.radius (fun j => |v j|-1/2) := norm_nonneg _
  nlinarith

theorem upper_count_signed (hc : CenterCertificate) (v : Momentum) (hv : SignedLocalBall v) :
    electricCount localMaterial v (1/4096) ≤ 2004 := by
  let P : Momentum → Prop := fun x => electricCount localMaterial x (1/4096) ≤ 2004
  have h01 (x : Momentum) : P (swap01 x) ↔ P x := by
    change electricCount localMaterial (swap01 x) (1/4096) ≤ 2004 ↔ _
    rw [show electricCount localMaterial (swap01 x) (1/4096) =
      electricCount localMaterial x (1/4096) from electricCount_generator (64*(7/256)) .swap01 x (1/4096)]
  have h12 (x : Momentum) : P (swap12 x) ↔ P x := by
    change electricCount localMaterial (swap12 x) (1/4096) ≤ 2004 ↔ _
    rw [show electricCount localMaterial (swap12 x) (1/4096) =
      electricCount localMaterial x (1/4096) from electricCount_generator (64*(7/256)) .swap12 x (1/4096)]
  have h0 (x : Momentum) : P (flip 0 x) ↔ P x := by
    have h := electricCount_generator (64*(7/256)) .reflect0 x (1/4096)
    rw [GlobalCubic.momentum_reflect0] at h
    change electricCount localMaterial (flip 0 x) (1/4096) =
      electricCount localMaterial x (1/4096) at h
    change electricCount localMaterial (flip 0 x) (1/4096) ≤ 2004 ↔ _
    rw [h]
  apply (abs_invariant P h01 h12 h0 v).mp
  have he : center+(fun j => |v j|-1/2) = fun j => |v j| := by
    ext j
    simp [center]
  simpa only [he] using upper_count_at_positive_center hc _ (abs_displacement_radius v hv)

theorem upper_count_reciprocal (hc : CenterCertificate) (c : Momentum) (hl : ReciprocalLocalBall c) :
    electricCount localMaterial c (1/4096) ≤ 2004 := by
  obtain ⟨v, n, rfl, hv⟩ := hl
  rw [electricCount_periodic]
  exact upper_count_signed hc v hv

/-- This discharges the actual two-band cardinality premise throughout all
four inequivalent L neighborhoods using finite center data only. -/
theorem actual_positive_count (hn : NegativeCenters) (hc : CenterCertificate)
    (c : Momentum) (hl : ReciprocalLocalBall c) :
    (Finset.univ.filter fun i =>
      0 < (electricFiber_symmetric Concrete.material (boundaryMomentum c)).eigenvalues rfl i ∧
      (electricFiber_symmetric Concrete.material (boundaryMomentum c)).eigenvalues rfl i < 7/256).card ≤ 2 :=
  LocalClusterCount.actual_positive_count c (global_negative_count hn c)
    (upper_count_reciprocal hc c hl)

theorem centered_positive_count (hn : NegativeCenters) (hc : CenterCertificate)
    (k : Translation) (q : Momentum) (hl : ReciprocalLocalBall (centeredMomentum k q)) :
    (Finset.univ.filter fun i =>
      0 < (YeeTaylorRemainder.centeredOperator_symmetric k q).eigenvalues rfl i ∧
      (YeeTaylorRemainder.centeredOperator_symmetric k q).eigenvalues rfl i < 7/256).card ≤ 2 := by
  apply positive_count_le_two _ _ (by norm_num) 2002
  · rw [← centered_threshold_count]
    exact actual_negative_count _ (global_negative_count hn _)
  · rw [← centered_threshold_count]
    exact actual_upper_count _ (upper_count_reciprocal hc _ hl)

end Maxwell.Spectral.UniformLocalNeighborhood
