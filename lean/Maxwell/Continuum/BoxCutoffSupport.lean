import Maxwell.Continuum.BoxCutoffDerivatives
import Maxwell.Continuum.BoxCellGeometry

/-! First and second derivatives of the actual cutoff are supported
in the explicitly counted outer cell layers. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.BoxCutoff

open CellGauge Filter Set
open scoped Topology

theorem schwartz_eventually_one (N : Fin 3 → ℝ) {x : Space}
    (hx : ∀ j, 2 < x j ∧ x j < N j-2) :
    (schwartz N : Space → ℂ) =ᶠ[𝓝 x] fun _ => 1 := by
  have hopen : IsOpen {y : Space | ∀ j, 2 < y j ∧ y j < N j-2} := by
    have hcoord (j : Fin 3) : Continuous (fun y : Space => y j) :=
      (PiLp.proj 2 (fun _ : Fin 3 => ℝ) j : Space →L[ℝ] ℝ).continuous
    simpa only [ofPred_forall, ← ofPred_and] using isOpen_iInter_of_finite (fun j : Fin 3 =>
      (isOpen_lt continuous_const (hcoord j)).inter (isOpen_lt (hcoord j) continuous_const))
  filter_upwards [hopen.mem_nhds hx] with y hy
  exact schwartz_one N (fun j => ⟨(hy j).1.le, (hy j).2.le⟩)

theorem partials_zero_of_locally_constant (θ : SchwartzMap Space ℂ) {x : Space} {c : ℂ}
    (hc : (θ : Space → ℂ) =ᶠ[𝓝 x] fun _ => c) (j k : Fin 3) :
    partialSchwartz j θ x = 0 ∧ partialSchwartz j (partialSchwartz k θ) x = 0 := by
  constructor
  · change fderiv ℝ θ x (coordinateDirection j) = 0
    rw [hc.fderiv_eq]
    simp
  · have hd : (partialSchwartz k θ : Space → ℂ) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [hc.fderiv (𝕜 := ℝ)] with y hy
      change fderiv ℝ θ y (coordinateDirection k) = 0
      rw [hy]
      simp
    change fderiv ℝ (partialSchwartz k θ) x (coordinateDirection j) = 0
    rw [hd.fderiv_eq]
    simp

theorem interior_of_not_boundaryCell (n : Fin 3 → ℕ) {x : Space}
    (hx : x ∈ tsupport (schwartz (side n))) (hn : cellIndex x ∉ boundaryCells n) :
    ∀ j, 2 < x j ∧ x j < side n j-2 := by
  classical
  have hb := schwartz_tsupport (side n) hx
  have hc : cellIndex x ∈ cells n := index_mem_cells n (fun j => by
    have hj : 1 ≤ x j ∧ x j ≤ side n j-1 := hb j (mem_univ j)
    exact ⟨by linarith [hj.1], by linarith [hj.2]⟩)
  have hnot : ¬ ∃ j, cellIndex x j ≤ 1 ∨ (n j : ℤ)-2 ≤ cellIndex x j :=
    fun he => hn (Finset.mem_filter.mpr ⟨hc, he⟩)
  intro j
  have hlo : 2 ≤ cellIndex x j := by
    have hh : ¬ cellIndex x j ≤ 1 := fun h => hnot ⟨j, Or.inl h⟩
    omega
  have hhi : cellIndex x j ≤ (n j : ℤ)-3 := by
    have hh : ¬ (n j : ℤ)-2 ≤ cellIndex x j := fun h => hnot ⟨j, Or.inr h⟩
    omega
  have hlor : (2 : ℝ) ≤ (cellIndex x j : ℝ) := by exact_mod_cast hlo
  have hhir : (cellIndex x j : ℝ) ≤ (n j : ℝ)-3 := by exact_mod_cast hhi
  have hs := (spatialBox_mem _ _).mp (mem_spatialBox_index x) j
  dsimp only [side]
  exact ⟨by linarith [hs.1], by linarith [hs.2]⟩

theorem cutoff_derivatives_supported (n : Fin 3 → ℕ) :
    (∀ j x, cellIndex x ∉ boundaryCells n → partialSchwartz j (schwartz (side n)) x = 0) ∧
    (∀ j k x, cellIndex x ∉ boundaryCells n →
      partialSchwartz j (partialSchwartz k (schwartz (side n))) x = 0) := by
  have hzero (j k : Fin 3) (x : Space) (hn : cellIndex x ∉ boundaryCells n) :
      partialSchwartz j (schwartz (side n)) x = 0 ∧
      partialSchwartz j (partialSchwartz k (schwartz (side n))) x = 0 := by
    by_cases hx : x ∈ tsupport (schwartz (side n))
    · exact partials_zero_of_locally_constant _
        (schwartz_eventually_one _ (interior_of_not_boundaryCell n hx hn)) j k
    · have hp (i : Fin 3) : tsupport (partialSchwartz i (schwartz (side n))) ⊆
          tsupport (schwartz (side n)) :=
        SchwartzMap.tsupport_lineDerivOp_subset (coordinateDirection i) _
      have hpp := (SchwartzMap.tsupport_lineDerivOp_subset (coordinateDirection j)
        (partialSchwartz k (schwartz (side n)))).trans (hp k)
      exact ⟨image_eq_zero_of_notMem_tsupport (fun hh => hx (hp j hh)),
        image_eq_zero_of_notMem_tsupport (fun hh => hx (hpp hh))⟩
  exact ⟨fun j x hx => (hzero j j x hx).1, fun j k x hx => (hzero j k x hx).2⟩

#print axioms cutoff_derivatives_supported

end Maxwell.Continuum.BoxCutoff
