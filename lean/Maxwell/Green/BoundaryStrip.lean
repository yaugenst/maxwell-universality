import Maxwell.TargetLattice
import Maxwell.Green.CombesThomas
import Maxwell.Green.FiniteBoundary

/-!
# The actual width-two PEC boundary strip

The finite operator is the principal compression of the infinite Yee
operator. Its restriction mismatch only reads exterior coordinates within
two lattice steps of a retained edge. This support statement is derived
from the two four-term curl stencils and exact scalar-material agreement.
-/

noncomputable section

namespace Maxwell.Green

open Maxwell.Spectral

@[simp] theorem siteDistance_self (x : Lattice.Site) : siteDistance x x = 0 := by
  simp [siteDistance]

theorem siteDistance_symm (x y : Lattice.Site) : siteDistance x y = siteDistance y x := by
  simp only [siteDistance, abs_sub_comm]

theorem siteDistance_triangle (x y z : Lattice.Site) :
    siteDistance x z ≤ siteDistance x y + siteDistance y z := by
  simpa only [← sitePoint_distance] using dist_triangle (sitePoint x) (sitePoint y) (sitePoint z)

/-- Dependence on field coordinates in a physical lattice neighborhood. -/
def HasSitePropagation (A : Lattice.Field →L[ℂ] Lattice.Field) (r : ℝ) : Prop :=
  ∀ (x y : Lattice.Field) (e : Lattice.Edge),
    (∀ f : Lattice.Edge, siteDistance f.2 e.2 ≤ r → x f = y f) → A x e = A y e

theorem fourPullbackCurl_propagation (p₁ p₂ p₃ p₄ : Equiv.Perm Lattice.Edge)
    (r : ℝ) (h₁ : ∀ e, siteDistance (p₁ e).2 e.2 ≤ r)
    (h₂ : ∀ e, siteDistance (p₂ e).2 e.2 ≤ r)
    (h₃ : ∀ e, siteDistance (p₃ e).2 e.2 ≤ r)
    (h₄ : ∀ e, siteDistance (p₄ e).2 e.2 ≤ r) :
    HasSitePropagation (fourPullbackCurl p₁ p₂ p₃ p₄) r := by
  intro x y e hxy
  change x (p₁ e) - x (p₂ e) - x (p₃ e) + x (p₄ e) =
    y (p₁ e) - y (p₂ e) - y (p₃ e) + y (p₄ e)
  rw [hxy _ (h₁ e), hxy _ (h₂ e), hxy _ (h₃ e), hxy _ (h₄ e)]

theorem inverse_permutation_propagation (p : Equiv.Perm Lattice.Edge) (r : ℝ)
    (hp : ∀ e, siteDistance (p e).2 e.2 ≤ r) :
    ∀ e, siteDistance (p.symm e).2 e.2 ≤ r := by
  intro e
  have h := hp (p.symm e)
  rw [p.apply_symm_apply, siteDistance_symm] at h
  exact h

theorem fourPullbackCurl_adjoint_propagation (p₁ p₂ p₃ p₄ : Equiv.Perm Lattice.Edge)
    (r : ℝ) (h₁ : ∀ e, siteDistance (p₁ e).2 e.2 ≤ r)
    (h₂ : ∀ e, siteDistance (p₂ e).2 e.2 ≤ r)
    (h₃ : ∀ e, siteDistance (p₃ e).2 e.2 ≤ r)
    (h₄ : ∀ e, siteDistance (p₄ e).2 e.2 ≤ r) :
    HasSitePropagation (fourPullbackCurl p₁ p₂ p₃ p₄).adjoint r := by
  have hid : (fourPullbackCurl p₁ p₂ p₃ p₄).adjoint =
      fourPullbackCurl p₁.symm p₂.symm p₃.symm p₄.symm := by
    simp [fourPullbackCurl]
  rw [hid]
  exact fourPullbackCurl_propagation _ _ _ _ r
    (inverse_permutation_propagation p₁ r h₁) (inverse_permutation_propagation p₂ r h₂)
    (inverse_permutation_propagation p₃ r h₃) (inverse_permutation_propagation p₄ r h₄)

theorem yeeCurl_propagation : HasSitePropagation Lattice.yeeCurl 1 := by
  apply fourPullbackCurl_propagation
  · intro e; exact (siteDistance_unit_step e.2 _).le
  · intro e; simp [Lattice.fieldPermutation]
  · intro e; exact (siteDistance_unit_step e.2 _).le
  · intro e; simp [Lattice.fieldPermutation]

theorem yeeCurl_adjoint_propagation : HasSitePropagation Lattice.yeeCurl.adjoint 1 := by
  apply fourPullbackCurl_adjoint_propagation
  · intro e; exact (siteDistance_unit_step e.2 _).le
  · intro e; simp [Lattice.fieldPermutation]
  · intro e; exact (siteDistance_unit_step e.2 _).le
  · intro e; simp [Lattice.fieldPermutation]

/-- The complete electric stencil has physical propagation radius two;
the scalar material multiplier does not enlarge the stencil. -/
theorem electricOperator_propagation (m : Lattice.Edge → ℝ) (K : ℝ)
    (hK : 0 ≤ K) (hm : ∀ e, |m e| ≤ K) :
    HasSitePropagation (Lattice.electricOperator m K hK hm) 2 := by
  intro x y e hxy
  have hcurl : ∀ f : Lattice.Edge, siteDistance f.2 e.2 ≤ 1 →
      Lattice.yeeCurl x f = Lattice.yeeCurl y f := by
    intro f hf
    apply yeeCurl_propagation x y f
    intro k hk
    apply hxy
    have ht := siteDistance_triangle k.2 f.2 e.2
    linarith
  have hgram := yeeCurl_adjoint_propagation _ _ e hcurl
  have heq : x e = y e := hxy e (by simp)
  change Lattice.yeeCurl.adjoint (Lattice.yeeCurl x) e -
      (1 / 64 : ℂ) * ((m e : ℂ) * x e) =
    Lattice.yeeCurl.adjoint (Lattice.yeeCurl y) e - (1 / 64 : ℂ) * ((m e : ℂ) * y e)
  rw [hgram, heq]

def retainedEdges (B : Target.Box) : Set Lattice.Edge := Set.range (Target.latticeEdge B)

/-- The exterior width-two strip, measured in the actual site metric. -/
def boundaryStrip (B : Target.Box) : Set Lattice.Edge :=
  {e | e ∉ retainedEdges B ∧ ∃ f ∈ retainedEdges B, siteDistance e.2 f.2 ≤ 2}

theorem edgeExtension_restriction_cut (B : Target.Box) :
    (Target.edgeExtension B).comp (Target.edgeRestriction B) = sequenceCut (retainedEdges B) := by
  classical
  ext x e
  change Target.sequenceExtensionLinear (Target.latticeEdge B)
      (Target.sequenceRestriction (Target.latticeEdge B) x) e = sequenceCut (retainedEdges B) x e
  by_cases he : e ∈ retainedEdges B
  · obtain ⟨i, rfl⟩ := he
    rw [Target.sequenceExtensionLinear_at, Target.sequenceRestriction_apply, sequenceCut_apply]
    simp [retainedEdges]
  · rw [Target.sequenceExtensionLinear_apply, sequenceCut_apply, ite_eq_right he]
    apply Finset.sum_eq_zero
    intro i _
    have hi : e ≠ Target.latticeEdge B i := by
      intro h; exact he ⟨i, h.symm⟩
    simp [hi]

theorem cut_complement_sub_id (s : Set Lattice.Edge) :
    sequenceCut s - ContinuousLinearMap.id ℂ Lattice.Field = -sequenceCut sᶜ := by
  classical
  ext x e
  by_cases he : e ∈ s <;> simp [sequenceCut_apply, he]

/-- Exact compression identifies the mismatch with propagation from the
exterior field. Scalar mass terms cancel on every retained coordinate. -/
theorem compression_boundaryMismatch (B : Target.Box)
    (A : EuclideanSpace ℂ B.Edge →L[ℂ] EuclideanSpace ℂ B.Edge)
    (H : Lattice.Field →L[ℂ] Lattice.Field)
    (hcompression : (Target.edgeRestriction B).comp (H.comp (Target.edgeExtension B)) = A) :
    boundaryMismatch A (Target.edgeRestriction B) H =
      -((Target.edgeRestriction B).comp (H.comp (sequenceCut (retainedEdges B)ᶜ))) := by
  have hcut := edgeExtension_restriction_cut B
  rw [← hcompression]
  ext1 x
  change Target.edgeRestriction B (H (Target.edgeExtension B (Target.edgeRestriction B x))) -
      Target.edgeRestriction B (H x) =
    -Target.edgeRestriction B (H (sequenceCut (retainedEdges B)ᶜ x))
  have hx := congrArg (fun F : Lattice.Field →L[ℂ] Lattice.Field => F x) hcut
  change Target.edgeExtension B (Target.edgeRestriction B x) = sequenceCut (retainedEdges B) x at hx
  rw [hx, ← map_sub, ← map_sub]
  have hs := congrArg (fun F : Lattice.Field →L[ℂ] Lattice.Field => F x)
    (cut_complement_sub_id (retainedEdges B))
  change sequenceCut (retainedEdges B) x - x = -sequenceCut (retainedEdges B)ᶜ x at hs
  rw [hs, map_neg, map_neg]

/-- The restriction mismatch reads only the actual exterior width-two strip.
Its support is proved from the Yee stencil, not passed as an assumption. -/
theorem yee_boundaryMismatch_support (B : Target.Box)
    (A : EuclideanSpace ℂ B.Edge →L[ℂ] EuclideanSpace ℂ B.Edge)
    (m : Lattice.Edge → ℝ) (K : ℝ) (hK : 0 ≤ K) (hm : ∀ e, |m e| ≤ K)
    (hcompression : (Target.edgeRestriction B).comp
      ((Lattice.electricOperator m K hK hm).comp (Target.edgeExtension B)) = A) :
    boundaryMismatch A (Target.edgeRestriction B) (Lattice.electricOperator m K hK hm) =
      (boundaryMismatch A (Target.edgeRestriction B)
        (Lattice.electricOperator m K hK hm)).comp (sequenceCut (boundaryStrip B)) := by
  classical
  rw [compression_boundaryMismatch B A _ hcompression]
  ext x i
  change -(Target.sequenceRestriction (Target.latticeEdge B)
      (Lattice.electricOperator m K hK hm (sequenceCut (retainedEdges B)ᶜ x)) i) =
    -(Target.sequenceRestriction (Target.latticeEdge B) (Lattice.electricOperator m K hK hm
      (sequenceCut (retainedEdges B)ᶜ (sequenceCut (boundaryStrip B) x))) i)
  rw [Target.sequenceRestriction_apply, Target.sequenceRestriction_apply]
  congr 1
  apply electricOperator_propagation
  intro e he
  by_cases hr : e ∈ retainedEdges B
  · simp [sequenceCut_apply, hr]
  · have hs : e ∈ boundaryStrip B := ⟨hr, Target.latticeEdge B i, ⟨i, rfl⟩, he⟩
    simp [sequenceCut_apply, hr, hs]

/-- The boundary mismatch has no volume or boundary-cardinality factor. -/
theorem compression_boundaryMismatch_norm_le (B : Target.Box)
    (A : EuclideanSpace ℂ B.Edge →L[ℂ] EuclideanSpace ℂ B.Edge)
    (H : Lattice.Field →L[ℂ] Lattice.Field)
    (hcompression : (Target.edgeRestriction B).comp (H.comp (Target.edgeExtension B)) = A) :
    ‖boundaryMismatch A (Target.edgeRestriction B) H‖ ≤ ‖H‖ := by
  rw [compression_boundaryMismatch B A H hcompression, norm_neg]
  calc
    _ ≤ ‖Target.edgeRestriction B‖ * ‖H.comp (sequenceCut (retainedEdges B)ᶜ)‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖Target.edgeRestriction B‖ * (‖H‖ * ‖sequenceCut (retainedEdges B)ᶜ‖) := by
      gcongr
      exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * (‖H‖ * 1) := by
      gcongr
      · exact Target.edgeRestriction_norm_le B
      · exact sequenceCut_norm_le _
    _ = ‖H‖ := by ring

def pecMaxwellOperator {B : Target.Box} (material : ScalarMaterial B.nx B.ny B.nz) :
    EuclideanSpace ℂ B.Edge →L[ℂ] EuclideanSpace ℂ B.Edge :=
  Matrix.toEuclideanCLM (n := B.Edge) (𝕜 := ℂ)
    ((Target.maxwell material).map fun q => (q : ℂ))

/-- Agreement of actual scalar cell values suffices to derive the entire
boundary support identity for the finite PEC Maxwell matrix. -/
theorem scalar_yee_boundaryMismatch_support {B : Target.Box}
    (material : ScalarMaterial B.nx B.ny B.nz) (m : Lattice.Site → ℝ)
    (hcell : ∀ c : B.Cell, m (Target.latticeCell c) = (material.value c : ℝ))
    (K : ℝ) (hK : 0 ≤ K) (hm : ∀ e, |Target.latticeEdgeAverage m e| ≤ K) :
    boundaryMismatch (pecMaxwellOperator material) (Target.edgeRestriction B)
      (Lattice.electricOperator (Target.latticeEdgeAverage m) K hK hm) =
    (boundaryMismatch (pecMaxwellOperator material) (Target.edgeRestriction B)
      (Lattice.electricOperator (Target.latticeEdgeAverage m) K hK hm)).comp
        (sequenceCut (boundaryStrip B)) :=
  yee_boundaryMismatch_support B _ _ K hK hm
    (Target.scalar_maxwell_matrix_compression material m hcell K hK hm)

theorem shifted_scalar_yee_boundaryMismatch_support {B : Target.Box}
    (material : ScalarMaterial B.nx B.ny B.nz) (m : Lattice.Site → ℝ)
    (hcell : ∀ c : B.Cell, m (Target.latticeCell c) = (material.value c : ℝ))
    (K : ℝ) (hK : 0 ≤ K) (hm : ∀ e, |Target.latticeEdgeAverage m e| ≤ K) (σ : ℂ) :
    boundaryMismatch
      (pecMaxwellOperator material - σ • ContinuousLinearMap.id ℂ (EuclideanSpace ℂ B.Edge))
      (Target.edgeRestriction B)
      (Lattice.electricOperator (Target.latticeEdgeAverage m) K hK hm -
        σ • ContinuousLinearMap.id ℂ Lattice.Field) =
    (boundaryMismatch
      (pecMaxwellOperator material - σ • ContinuousLinearMap.id ℂ (EuclideanSpace ℂ B.Edge))
      (Target.edgeRestriction B)
      (Lattice.electricOperator (Target.latticeEdgeAverage m) K hK hm -
        σ • ContinuousLinearMap.id ℂ Lattice.Field)).comp (sequenceCut (boundaryStrip B)) := by
  rw [boundaryMismatch_shift]
  exact scalar_yee_boundaryMismatch_support material m hcell K hK hm

/-- The strip inherits separation from the entire exterior set; this
intermediate theorem is specialized to Cartesian box margins below. -/
theorem boundaryStrip_separation (B : Target.Box) (source : Set Lattice.Edge) (d : ℝ)
    (hbuffer : ∀ f ∈ source, ∀ e ∉ retainedEdges B, d ≤ siteDistance e.2 f.2) :
    ∀ e ∈ boundaryStrip B, ∀ f ∈ source, d ≤ siteDistance e.2 f.2 := by
  intro e he f hf
  exact hbuffer f hf e he.1

theorem sequenceCut_extension {ι : Type*} [Fintype ι] [DecidableEq ι]
    (embedding : ι ↪ Lattice.Edge) :
    (sequenceCut (Set.range embedding)).comp
      (Target.sequenceExtension embedding).toContinuousLinearMap =
      (Target.sequenceExtension embedding).toContinuousLinearMap := by
  classical
  ext x e
  change sequenceCut (Set.range embedding) (Target.sequenceExtensionLinear embedding x) e = _
  by_cases he : e ∈ Set.range embedding
  · simp only [sequenceCut_apply, ite_eq_left he]
    rfl
  · rw [sequenceCut_apply, ite_eq_right he]
    change 0 = Target.sequenceExtensionLinear embedding x e
    rw [Target.sequenceExtensionLinear_apply]
    symm
    apply Finset.sum_eq_zero
    intro i _
    have hi : e ≠ embedding i := by intro h; exact he ⟨i, h.symm⟩
    simp [hi]

/-- A finite source injection receives the same count-free strip bound
as the complete coordinate source set. -/
theorem cut_resolvent_extension_norm_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (embedding : ι ↪ Lattice.Edge) (target : Set Lattice.Edge)
    (R : Lattice.Field ≃L[ℂ] Lattice.Field) (bound : ℝ)
    (hbound : ‖(sequenceCut target).comp ((R.symm : Lattice.Field →L[ℂ] Lattice.Field).comp
      (sequenceCut (Set.range embedding)))‖ ≤ bound) :
    ‖(sequenceCut target).comp ((R.symm : Lattice.Field →L[ℂ] Lattice.Field).comp
      (Target.sequenceExtension embedding).toContinuousLinearMap)‖ ≤ bound := by
  have hid : (sequenceCut target).comp ((R.symm : Lattice.Field →L[ℂ] Lattice.Field).comp
      (Target.sequenceExtension embedding).toContinuousLinearMap) =
    ((sequenceCut target).comp ((R.symm : Lattice.Field →L[ℂ] Lattice.Field).comp
      (sequenceCut (Set.range embedding)))).comp
        (Target.sequenceExtension embedding).toContinuousLinearMap := by
    rw [ContinuousLinearMap.comp_assoc, ContinuousLinearMap.comp_assoc, sequenceCut_extension]
  rw [hid]
  calc
    _ ≤ ‖(sequenceCut target).comp ((R.symm : Lattice.Field →L[ℂ] Lattice.Field).comp
        (sequenceCut (Set.range embedding)))‖ *
      ‖(Target.sequenceExtension embedding).toContinuousLinearMap‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖(sequenceCut target).comp ((R.symm : Lattice.Field →L[ℂ] Lattice.Field).comp
        (sequenceCut (Set.range embedding)))‖ * 1 := by
      gcongr
      exact Target.sequenceExtension_norm_le embedding
    _ ≤ bound := by simpa using hbound

/-- Side lengths in the same coordinate order as the integer lattice. -/
def boxSide (B : Target.Box) (i : Fin 3) : ℕ := ![B.nx, B.ny, B.nz] i

/-- Every orientation at a site strictly inside all three box walls is a
retained PEC edge. This uses the actual transverse `+1` indexing. -/
theorem interior_site_retained (B : Target.Box) (e : Lattice.Edge)
    (hinside : ∀ i, 0 < e.2 i ∧ e.2 i < (boxSide B i : ℤ)) :
    e ∈ retainedEdges B := by
  rcases e with ⟨d, x⟩
  have h0 := hinside 0
  have h1 := hinside 1
  have h2 := hinside 2
  simp [boxSide] at h0 h1 h2
  fin_cases d
  · let i : Fin B.nx := ⟨(x 0).toNat, by omega⟩
    let j : Fin (B.ny - 1) := ⟨(x 1 - 1).toNat, by omega⟩
    let k : Fin (B.nz - 1) := ⟨(x 2 - 1).toNat, by omega⟩
    refine ⟨Sum.inl (i, j, k), ?_⟩
    change (0, ![((x 0).toNat : ℤ), ((x 1 - 1).toNat : ℤ) + 1,
      ((x 2 - 1).toNat : ℤ) + 1]) = (0, x)
    congr 1
    ext q
    fin_cases q <;> simp <;> omega
  · let i : Fin (B.nx - 1) := ⟨(x 0 - 1).toNat, by omega⟩
    let j : Fin B.ny := ⟨(x 1).toNat, by omega⟩
    let k : Fin (B.nz - 1) := ⟨(x 2 - 1).toNat, by omega⟩
    refine ⟨Sum.inr (Sum.inl (i, j, k)), ?_⟩
    change (1, ![((x 0 - 1).toNat : ℤ) + 1, ((x 1).toNat : ℤ),
      ((x 2 - 1).toNat : ℤ) + 1]) = (1, x)
    congr 1
    ext q
    fin_cases q <;> simp <;> omega
  · let i : Fin (B.nx - 1) := ⟨(x 0 - 1).toNat, by omega⟩
    let j : Fin (B.ny - 1) := ⟨(x 1 - 1).toNat, by omega⟩
    let k : Fin B.nz := ⟨(x 2).toNat, by omega⟩
    refine ⟨Sum.inr (Sum.inr (i, j, k)), ?_⟩
    change (2, ![((x 0 - 1).toNat : ℤ) + 1, ((x 1 - 1).toNat : ℤ) + 1,
      ((x 2).toNat : ℤ)]) = (2, x)
    congr 1
    ext q
    fin_cases q <;> simp <;> omega

theorem exterior_has_wall_coordinate (B : Target.Box) (e : Lattice.Edge)
    (he : e ∉ retainedEdges B) :
    ∃ i : Fin 3, e.2 i ≤ 0 ∨ (boxSide B i : ℤ) ≤ e.2 i := by
  by_contra h
  push Not at h
  exact he (interior_site_retained B e h)

/-- Actual Cartesian source margins imply separation from every exterior
edge, simultaneously for the full source union. -/
theorem coordinate_margin_exterior_separation (B : Target.Box) (source : Set Lattice.Edge)
    (r : ℝ) (hmargin : ∀ f ∈ source, ∀ i : Fin 3,
      r ≤ (f.2 i : ℝ) ∧ (f.2 i : ℝ) + r ≤ (boxSide B i : ℝ)) :
    ∀ f ∈ source, ∀ e ∉ retainedEdges B, r ≤ siteDistance e.2 f.2 := by
  intro f hf e he
  obtain ⟨i, hi⟩ := exterior_has_wall_coordinate B e he
  have hm := hmargin f hf i
  have hcoord : r ≤ |(e.2 i : ℝ) - (f.2 i : ℝ)| := by
    rcases hi with hi | hi
    · have hir : (e.2 i : ℝ) ≤ 0 := by exact_mod_cast hi
      calc
        r ≤ (f.2 i : ℝ) - (e.2 i : ℝ) := by linarith
        _ ≤ |(e.2 i : ℝ) - (f.2 i : ℝ)| := by
          rw [abs_sub_comm]
          exact le_abs_self _
    · have hir : (boxSide B i : ℝ) ≤ (e.2 i : ℝ) := by exact_mod_cast hi
      exact (show r ≤ (e.2 i : ℝ) - (f.2 i : ℝ) by linarith).trans (le_abs_self _)
  apply hcoord.trans
  unfold siteDistance
  exact Finset.single_le_sum (fun j _ => abs_nonneg ((e.2 j : ℝ) - (f.2 j : ℝ)))
    (Finset.mem_univ i)

theorem coordinate_margin_strip_separation (B : Target.Box) (source : Set Lattice.Edge)
    (r : ℝ) (hmargin : ∀ f ∈ source, ∀ i : Fin 3,
      r ≤ (f.2 i : ℝ) ∧ (f.2 i : ℝ) + r ≤ (boxSide B i : ℝ)) :
    ∀ e ∈ boundaryStrip B, ∀ f ∈ source, r ≤ siteDistance e.2 f.2 :=
  boundaryStrip_separation B source r (coordinate_margin_exterior_separation B source r hmargin)

/-- Complete finite/infinite background compression estimate for actual
scalar PEC matrices and finite coordinate sources. Cartesian wall margins
discharge both the strip separation and boundary-support obligations. The
finite inverse bound and the unshifted infinite gap remain explicit inputs. -/
theorem finite_background_error_of_coordinate_margin
    {B : Target.Box} {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (material : ScalarMaterial B.nx B.ny B.nz) (m : Lattice.Site → ℝ)
    (hcell : ∀ c : B.Cell, m (Target.latticeCell c) = (material.value c : ℝ))
    (M : ℝ) (hM : 0 ≤ M) (hm : ∀ e, |Target.latticeEdgeAverage m e| ≤ M)
    (A : EuclideanSpace ℂ B.Edge ≃L[ℂ] EuclideanSpace ℂ B.Edge)
    (H : Lattice.Field ≃L[ℂ] Lattice.Field) (σ : ℂ)
    (hA : (A : EuclideanSpace ℂ B.Edge →L[ℂ] EuclideanSpace ℂ B.Edge) =
      pecMaxwellOperator material - σ • ContinuousLinearMap.id ℂ (EuclideanSpace ℂ B.Edge))
    (hH : (H : Lattice.Field →L[ℂ] Lattice.Field) =
      Lattice.electricOperator (Target.latticeEdgeAverage m) M hM hm)
    (embedding : ι ↪ Lattice.Edge)
    (Q : EuclideanSpace ℂ B.Edge →L[ℂ] EuclideanSpace ℂ ι) (hQ : ‖Q‖ ≤ 1)
    (g τ J L μ buffer : ℝ) (hg : 0 < g) (hμ : 0 ≤ μ) (hbuffer : 0 ≤ buffer)
    (hmargin : ∀ i : ι, ∀ j : Fin 3,
      buffer ≤ ((embedding i).2 j : ℝ) ∧
        ((embedding i).2 j : ℝ) + buffer ≤ (boxSide B j : ℝ))
    (hinv : ‖(H.symm : Lattice.Field →L[ℂ] Lattice.Field)‖ ≤ 1 / g)
    (hfinite : ‖(A.symm : EuclideanSpace ℂ B.Edge →L[ℂ] EuclideanSpace ℂ B.Edge)‖ ≤ L)
    (hnorm : ‖(H : Lattice.Field →L[ℂ] Lattice.Field)‖ ≤ J)
    (hτ : ‖σ‖ ≤ τ) (hσ : ‖σ‖ ≤ g / 4)
    (hsmall : 16 * (Real.exp (2 * μ) - 1) ≤ g / 4) :
    ‖Q.comp ((A.symm : EuclideanSpace ℂ B.Edge →L[ℂ] EuclideanSpace ℂ B.Edge).comp
        ((Target.edgeRestriction B).comp (Target.sequenceExtension embedding).toContinuousLinearMap)) -
      (Q.comp (Target.edgeRestriction B)).comp ((H.symm : Lattice.Field →L[ℂ] Lattice.Field).comp
        (Target.sequenceExtension embedding).toContinuousLinearMap)‖ ≤
      2 * τ / g ^ 2 + (4 * J * L / g) * Real.exp (-μ * buffer) := by
  have hsep : ∀ e ∈ boundaryStrip B, ∀ f ∈ Set.range embedding,
      buffer ≤ siteDistance e.2 f.2 := by
    apply coordinate_margin_strip_separation
    rintro f ⟨i, rfl⟩ j
    exact hmargin i j
  obtain ⟨R, hR, hRnorm, htail⟩ := exists_shifted_yee_set_to_set_resolvent H
    (Target.latticeEdgeAverage m) M hM hm hH (Set.range embedding) (boundaryStrip B)
    (Set.range_nonempty _) buffer buffer μ g hbuffer le_rfl hμ hg hsep hinv σ hσ hsmall
  have hsupport : boundaryMismatch A (Target.edgeRestriction B) R =
      (boundaryMismatch A (Target.edgeRestriction B) R).comp (sequenceCut (boundaryStrip B)) := by
    rw [hA, hR, hH]
    exact shifted_scalar_yee_boundaryMismatch_support material m hcell M hM hm σ
  have hboundarynorm : ‖boundaryMismatch A (Target.edgeRestriction B) R‖ ≤ 2 * J := by
    rw [hA, hR, hH, boundaryMismatch_shift]
    have hc := Target.scalar_maxwell_matrix_compression material m hcell M hM hm
    have hn := compression_boundaryMismatch_norm_le B (pecMaxwellOperator material)
      (Lattice.electricOperator (Target.latticeEdgeAverage m) M hM hm) hc
    rw [← hH] at hn
    rw [← hH]
    exact hn.trans (show ‖(H : Lattice.Field →L[ℂ] Lattice.Field)‖ ≤ 2 * J by
      linarith [norm_nonneg (H : Lattice.Field →L[ℂ] Lattice.Field)])
  exact finite_background_compression_error A H R (Target.edgeRestriction B) Q
    (Target.sequenceExtension embedding).toContinuousLinearMap (sequenceCut (boundaryStrip B)) σ
    hR hsupport g τ J L μ buffer hg hτ (Target.edgeRestriction_norm_le B) hQ
    (Target.sequenceExtension_norm_le embedding) hfinite hinv hRnorm hboundarynorm
    (cut_resolvent_extension_norm_le embedding (boundaryStrip B) R _ htail)

end Maxwell.Green
