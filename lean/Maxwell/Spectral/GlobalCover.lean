import Maxwell.Spectral.GlobalComparison
import Maxwell.Spectral.GlobalCubic
import Maxwell.Spectral.GammaNegative
import Maxwell.Certificate.NegativeCover.Complete
import Maxwell.Certificate.NegativeScalar.Verified
import Maxwell.Certificate.CoverDataComplete
import Maxwell.Certificate.GlobalGeometry

/-! The two kernel-checked geometric covers are connected to the actual
primitive Yee spectrum. The remaining finite inputs are precisely the center
trial-vector inequalities, rather than whole-box spectral assertions. -/

noncomputable section
namespace Maxwell.Spectral.GlobalCover
open Maxwell.Certificate Maxwell.Certificate.FourierBinding
open Maxwell.Spectral.PeriodicYee (Momentum Cell20)
open Maxwell.Spectral.PrimitiveYee
open BoxNeighborhood GlobalComparison ReciprocalCover

/-- Actual electric eigenvalue count at a real energy threshold. -/
def electricCount (material : Cell20 → ℝ) (c : Momentum) (s : ℝ) : ℕ :=
  (Finset.univ.filter fun i =>
    (electricFiber_symmetric material (boundaryMomentum c)).eigenvalues rfl i < s).card

private theorem count_congr {A B : FourierSpace →ₗ[ℂ] FourierSpace}
    (hAB : A = B) (hA : A.IsSymmetric) (hB : B.IsSymmetric) (s : ℝ) :
    (Finset.univ.filter fun i => hA.eigenvalues rfl i < s).card =
      (Finset.univ.filter fun i => hB.eigenvalues rfl i < s).card := by
  subst B
  rfl

theorem electricCount_periodic (material : Cell20 → ℝ) (c : Momentum)
    (n : Translation) (s : ℝ) :
    electricCount material (c+reciprocalShift n) s = electricCount material c s := by
  exact count_congr (congrArg (fun A : Matrix Electric Electric ℂ => A.toEuclideanLin)
    (fiber_reciprocal_periodic material c n)) _ _ s

theorem electricCount_generator (shift : ℝ) (g : GlobalCubic.Generator) (c : Momentum)
    (s : ℝ) :
    electricCount (GlobalCubic.comparator shift) (GlobalCubic.momentum g c) s =
      electricCount (GlobalCubic.comparator shift) c s := by
  unfold electricCount
  rw [← GlobalCubic.comparator_eigenvalues shift g c
    (electricFiber_symmetric _ _) (electricFiber_symmetric _ _)]

private theorem base_eq_comparator : Concrete.baseMaterial = GlobalCubic.comparator 0 := by
  ext r
  simp [GlobalCubic.comparator]

/-- The exact remaining finite inputs for the original-material cover. -/
def NegativeCenters : Prop := ∀ i : Fin 604,
  ∃ Fn : NegativeCoordinates →L[ℂ] BoxMagnetic.Field,
    BoxNegativeNeighborhood.NegativeCenterBounds Concrete.baseMaterial (FrozenNegative.center i)
      (NegativeScalar.Frozen.constants i) Fn

/-- Finite center certificates for the shifted-comparator boxes. All fields
are scalar inequalities or center trial-vector bounds. -/
def ComparatorBoxCertificates : Prop := ∀ i : Fin 2056,
  ∃ (b : Constants) (low : Finset Frequency) (Fn : NegativeCoordinates →L[ℂ] BoxMagnetic.Field)
      (Fp : PositiveCoordinates low →L[ℂ] BoxMagnetic.Field),
    Accepted b ∧ (∀ j, b.half j = FrozenGlobal.half i j) ∧ b.σ = 1/2^24 ∧
      CenterBounds comparatorMaterial (FrozenGlobal.center i) low b Fn Fp

theorem negative_box_count (hcenters : NegativeCenters) (i : Fin 604) (x : Momentum)
    (hx : (FrozenNegativeCover.matrixBoxes i).Contains x) :
    2002 ≤ electricCount Concrete.baseMaterial x (-1/4096) := by
  obtain ⟨Fn, hFn⟩ := hcenters i
  have h := BoxNegativeNeighborhood.electric_energy_count (NegativeScalar.Frozen.accepted i)
    hFn (fun e => (base_edge_bounds e).1) (x-FrozenNegative.center i) (fun j => by
      rw [NegativeScalar.Frozen.constants_half]
      exact FrozenNegative.box_displacement i x hx j)
  rw [FrozenNegative.point_eq_center_add_displacement] at h
  change 2002 ≤ electricCount Concrete.baseMaterial x (-(1/4096)) at h
  simpa only [neg_div] using h

theorem negative_gamma_count (x : Momentum) (hx : ∀ j, |x j| ≤ 3/16) :
    2002 ≤ electricCount Concrete.baseMaterial x (-1/4096) := by
  simpa only [electricCount, neg_div] using (GammaNegative.magnetic_negative_count Concrete.baseMaterial
    (fun e => (base_edge_bounds e).1) x hx).trans
    (MagneticThreshold.energy_threshold_lower Concrete.baseMaterial
      (fun e => (base_edge_bounds e).1) x (1/4096) (by norm_num) (by norm_num))

/-- The clean cover gives the lower-band count at every momentum, using
actual reciprocal periodicity and the proved affine cubic symmetries. -/
theorem global_negative_count (hcenters : NegativeCenters) (c : Momentum) :
    2002 ≤ electricCount Concrete.baseMaterial c (-1/4096) := by
  apply of_wedge (fun x => 2002 ≤ electricCount Concrete.baseMaterial x (-1/4096))
  · intro x n
    rw [electricCount_periodic]
  · intro x
    rw [base_eq_comparator, ← GlobalCubic.momentum_swap01,
      electricCount_generator]
  · intro x
    rw [base_eq_comparator, ← GlobalCubic.momentum_swap12,
      electricCount_generator]
  · intro x
    rw [base_eq_comparator, ← GlobalCubic.momentum_reflect0,
      electricCount_generator]
  · intro x hx hw
    rcases FrozenNegativeCover.coverage x hx hw with hg | ⟨i, hi⟩
    · apply negative_gamma_count x
      intro j
      rw [abs_of_nonneg (hx j).1]
      exact hg j
    · exact negative_box_count hcenters i x hi

/-- The upper endpoint of an accepted box bounds the physical electric
count below the positive energy margin, including its endpoint. -/
theorem accepted_box_upper_count {material : Cell20 → ℝ} {c : Momentum}
    {low : Finset Frequency} {b : Constants}
    {Fn : NegativeCoordinates →L[ℂ] BoxMagnetic.Field}
    {Fp : PositiveCoordinates low →L[ℂ] BoxMagnetic.Field}
    (hb : Accepted b) (hc : CenterBounds material c low b Fn Fp)
    (hm : ∀ e, 1 ≤ edgeAverage material e ∧ edgeAverage material e ≤ 13)
    (q : Momentum) (hbox : ∀ j, |q j| ≤ b.half j) :
    electricCount material (c+q) b.σ ≤ 2002 := by
  have hq := BoxGeometry.displacementSize_le_of_box_radius q b.half b.s hbox hb.size_bound
  have hlap := BoxGeometry.shifted_laplacianSymbol_ne_zero c q b.s b.r hq hb.small_low hc.symbol_low
  have ht : 0 < 1/64+b.σ := by linarith [hb.sigma_nonneg]
  have hshift : |(1/64+b.σ)-1/64| ≤ b.σ := by
    rw [add_sub_cancel_left, abs_of_nonneg hb.sigma_nonneg]
  have hT := (accepted_box_transverse_inertia hb hc hm q (1/64+b.σ) hbox hshift).1
  have hM : (Finset.univ.filter fun i =>
      (shiftedMagneticFourier_symmetric material (c+q) (1/64+b.σ)).eigenvalues rfl i < 0).card = 2002 := by
    rw [shiftedMagneticFourier_negative_count material (c+q) (1/64+b.σ) ht hlap, hT]
  exact (MagneticThreshold.energy_threshold_upper material (fun e => (hm e).1)
    (c+q) b.σ hb.sigma_nonneg).trans_eq hM

theorem comparator_box_count (hcenters : ComparatorBoxCertificates) (i : Fin 2056) (x : Momentum)
    (hx : (FrozenCover.matrixBoxes i).Contains x) :
    electricCount comparatorMaterial x (1/2^24) ≤ 2002 := by
  obtain ⟨b, low, Fn, Fp, hb, hhalf, hsigma, hF⟩ := hcenters i
  have h := accepted_box_upper_count hb hF
    comparator_edge_bounds (x-FrozenGlobal.center i) (fun j => by
      rw [hhalf]
      exact FrozenGlobal.box_displacement i x hx j)
  rw [FrozenGlobal.point_eq_center_add_displacement, hsigma] at h
  exact h

theorem comparator_gamma_count (x : Momentum) (hx : ∀ j, |x j| ≤ 1/8) :
    electricCount comparatorMaterial x (1/2^24) ≤ 2002 := by
  have hM := (GammaInertia.gamma_magnetic_inertia comparatorMaterial comparator_edge_bounds x hx
    (1/64+1/2^24) (by norm_num)).1
  exact (MagneticThreshold.energy_threshold_upper comparatorMaterial
    (fun e => (comparator_edge_bounds e).1) x (1/2^24) (by norm_num)).trans_eq hM


/-- The eight signed Cartesian L points, before identifying reciprocal pairs. -/
def SignedLocalBall (v : Momentum) : Prop :=
  ∃ s : Translation, (∀ j, s j = 1 ∨ s j = -1) ∧
    (∑ j, (v j-(s j : ℝ)/2)^2) ≤ 1/400

/-- A genuine reciprocal translate of one of the four local L neighborhoods. -/
def ReciprocalLocalBall (c : Momentum) : Prop :=
  ∃ (v : Momentum) (n : Translation), c = v+reciprocalShift n ∧ SignedLocalBall v

private theorem comparator_count_swap01 (c : Momentum) (t : ℝ) :
    electricCount comparatorMaterial (swap01 c) t = electricCount comparatorMaterial c t := by
  exact electricCount_generator (64*(157/16384)) .swap01 c t

private theorem comparator_count_swap12 (c : Momentum) (t : ℝ) :
    electricCount comparatorMaterial (swap12 c) t = electricCount comparatorMaterial c t := by
  exact electricCount_generator (64*(157/16384)) .swap12 c t

private theorem comparator_count_flip0 (c : Momentum) (t : ℝ) :
    electricCount comparatorMaterial (flip 0 c) t = electricCount comparatorMaterial c t := by
  have h := electricCount_generator (64*(157/16384)) .reflect0 c t
  rw [GlobalCubic.momentum_reflect0] at h
  exact h

/-- The shifted comparator cover, with its local leaves retained as exact
Cartesian balls. No symmetry of the perturbed material is assumed. -/
theorem comparator_count_or_signed_ball (hcenters : ComparatorBoxCertificates)
    (v : Momentum) (hv : ∀ j, |v j| ≤ 1) (hs : (∑ j, |v j|) ≤ 3/2) :
    electricCount comparatorMaterial v (1/2^24) ≤ 2002 ∨ SignedLocalBall v := by
  let P : Momentum → Prop := fun x => electricCount comparatorMaterial x (1/2^24) ≤ 2002
  have h01 (x : Momentum) : P (swap01 x) ↔ P x := by
    dsimp only [P]
    rw [comparator_count_swap01]
  have h12 (x : Momentum) : P (swap12 x) ↔ P x := by
    dsimp only [P]
    rw [comparator_count_swap12]
  have h0 (x : Momentum) : P (flip 0 x) ↔ P x := by
    dsimp only [P]
    rw [comparator_count_flip0]
  have htrans : P (sort (fun j => |v j|)) ↔ P v :=
    (sort_invariant P h01 h12 _).trans (abs_invariant P h01 h12 h0 v)
  have hb := sort_bounds (fun j => |v j|) 0 1 (fun j => ⟨abs_nonneg _, hv j⟩)
  have hw := sort_wedge (fun j => |v j|) hs
  rcases FrozenCover.coverage _ hb hw with hg | hl | ⟨i, hi⟩
  · left
    apply htrans.mp
    apply comparator_gamma_count
    intro j
    rw [abs_of_nonneg (hb j).1]
    exact hg j
  · exact Or.inr (signed_local_ball v hl)
  · exact Or.inl (htrans.mp (comparator_box_count hcenters i _ hi))

/-- The positive-band count holds globally outside the actual local edge balls. -/
theorem comparator_count_or_local (hcenters : ComparatorBoxCertificates) (c : Momentum) :
    electricCount comparatorMaterial c (1/2^24) ≤ 2002 ∨ ReciprocalLocalBall c := by
  obtain ⟨v, hv, hs, n, hn⟩ := exists_voronoi_representative c
  rcases comparator_count_or_signed_ball hcenters v hv hs with h | h
  · left
    rw [hn, electricCount_periodic]
    exact h
  · exact Or.inr ⟨v, n, hn, h⟩

/-- Every actual perturbed eigenvalue outside the four local edge
neighborhoods has the stated uniform separation from the selected edge. -/
theorem global_edge_gap (hn : NegativeCenters) (hp : ComparatorBoxCertificates)
    (c : Momentum) (hc : ¬ ReciprocalLocalBall c)
    (i : Fin (Module.finrank ℂ FourierSpace)) :
    1/500000 ≤ |(electricFiber_symmetric Concrete.material (boundaryMomentum c)).eigenvalues rfl i-
      PointWitness.pointEnergy| := by
  have hhi := (comparator_count_or_local hp c).resolve_right hc
  exact actual_edge_gap c (global_negative_count hn c) hhi i

/-- Actual inverse existence on the global complement follows from the
finite center trial checks and the proved Gamma and cover analysis. -/
theorem global_edge_invertible (hn : NegativeCenters) (hp : ComparatorBoxCertificates)
    (c : Momentum) (hc : ¬ ReciprocalLocalBall c) :
    (Matrix.toEuclideanCLM (n := Electric) (𝕜 := ℂ)
      (fiber Concrete.material (boundaryMomentum c)) - (PointWitness.pointEnergy : ℂ) • 1).IsInvertible := by
  have hhi := (comparator_count_or_local hp c).resolve_right hc
  exact actual_edge_invertible c (global_negative_count hn c) hhi

end Maxwell.Spectral.GlobalCover
