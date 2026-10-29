import Maxwell.Composition.SourceSeedSupport

/-! A source seed is a collision-free stream of exactly n times the fixed
prototype's edge count. Each value uses the original exact normalized RHS. -/
noncomputable section
namespace Maxwell.Composition.SourceSeedStream
open Maxwell.Composition.PhysicalGram Maxwell.Composition.PhysicalSource
open Maxwell.Defect Maxwell.Logical
open scoped BigOperators
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 1000000

variable (P : PhysicalPlatform) (S : Source.SparseSystem) (precision d : ℕ)
variable (ζ : ℚ) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
variable (hd : P.spacing.minimumDistance ≤ d)

abbrev Index := Fin S.n × Local P

def edge (ik : Index P S) : (box P S precision d ζ hζ hζ1).Edge :=
  (layout P S precision d ζ hζ hζ1 hd).pick (SourceSeedSupport.vertex S precision ik.1,ik.2)

def value (q : Local P → ℚ) (ik : Index P S) : ℚ :=
  (ScalarDefect.coordinateWeight P.defect ik.2)⁻¹ *
    (q ik.2 * Normalization.normalizedSource S ik.1)

theorem edge_injective : Function.Injective (edge P S precision d ζ hζ hζ1 hd) := by
  intro i j h
  have he := (layout P S precision d ζ hζ hζ1 hd).injective h
  have h1 := congrArg (fun x : Sites S precision × Local P => x.1) he
  have h2 := congrArg (fun x : Sites S precision × Local P => x.2) he
  exact Prod.ext (SourceSeedSupport.vertex_injective S precision h1) h2

/-- The full-site definition equals the n-by-local-edge record stream. -/
theorem seed_eq (q : Local P → ℚ) (e : (box P S precision d ζ hζ hζ1).Edge) :
    seed P S precision d ζ hζ hζ1 hd q (SourceRational.decorated S precision) e =
      ∑ ik : Index P S, if edge P S precision d ζ hζ hζ1 hd ik = e then value P S q ik else 0 := by
  classical
  unfold seed
  rw [Fintype.sum_prod_type]
  calc
    _ = ∑ k : Local P, ∑ i : Sites S precision,
        (if (layout P S precision d ζ hζ hζ1 hd).pick (i,k) = e then
          (ScalarDefect.coordinateWeight P.defect k)⁻¹ * q k else 0) *
            SourceRational.decorated S precision i := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro i _
      rw [shared_weight]
      split_ifs <;> ring
    _ = ∑ k : Local P, ∑ i : Fin S.n,
        (if (layout P S precision d ζ hζ hζ1 hd).pick
          (SourceSeedSupport.vertex S precision i,k) = e then
          (ScalarDefect.coordinateWeight P.defect k)⁻¹ * q k else 0) *
            Normalization.normalizedSource S i := by
      apply Finset.sum_congr rfl
      intro k _
      exact SourceSeedSupport.weighted_sum S precision _
    _ = _ := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro i _
      change (if (layout P S precision d ζ hζ hζ1 hd).pick
          (SourceSeedSupport.vertex S precision k,i) = e then
          (ScalarDefect.coordinateWeight P.defect i)⁻¹ * q i else 0) *
          Normalization.normalizedSource S k =
        if (layout P S precision d ζ hζ hζ1 hd).pick
          (SourceSeedSupport.vertex S precision k,i) = e then
          (ScalarDefect.coordinateWeight P.defect i)⁻¹ *
            (q i * Normalization.normalizedSource S k) else 0
      split_ifs <;> ring

theorem seed_at (q : Local P → ℚ) (ik : Index P S) :
    seed P S precision d ζ hζ hζ1 hd q (SourceRational.decorated S precision)
      (edge P S precision d ζ hζ hζ1 hd ik) = value P S q ik := by
  classical
  rw [seed_eq]
  simp only [(edge_injective P S precision d ζ hζ hζ1 hd).eq_iff]
  simp

theorem seed_off (q : Local P → ℚ) (e : (box P S precision d ζ hζ hζ1).Edge)
    (he : ∀ ik, edge P S precision d ζ hζ hζ1 hd ik ≠ e) :
    seed P S precision d ζ hζ hζ1 hd q (SourceRational.decorated S precision) e = 0 := by
  rw [seed_eq]
  simp only [he, ite_false, Finset.sum_const_zero]

end Maxwell.Composition.SourceSeedStream
