import Maxwell.Defect.FiniteCompressionSpectral
import Maxwell.Green.Volume
import Mathlib.Data.List.Dedup
import Mathlib.Data.Finset.Card

/-! A finite rational inverse-polynomial implementation that combines
repeated lattice edges at every iteration. Its support grows cubically in
the degree, rather than storing an exponentially growing list of paths. -/
namespace Maxwell.Defect.FiniteStencil
open Spectral Spectral.Lattice
set_option maxHeartbeats 600000

/-- Combine every repeated edge using exact rational addition. -/
def compact (v : SparseField) : SparseField :=
  (v.map Prod.fst).dedup.map fun e => (e, evaluate v e)

private theorem sum_unique_coordinates (l : List Edge) (hl : l.Nodup) (f : Edge → ℚ) (e : Edge) :
    (l.map fun a => if e = a then f a else 0).sum = if e ∈ l then f e else 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha := List.nodup_cons.mp hl
    rw [List.map_cons, List.sum_cons, ih ha.2]
    by_cases hea : e = a
    · subst e
      simp [ha.1]
    · simp [hea]

theorem evaluate_eq_zero_of_not_mem (v : SparseField) (e : Edge)
    (he : e ∉ v.map Prod.fst) : evaluate v e = 0 := by
  unfold evaluate
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
  have hn : e ≠ t.1 := by
    intro h
    exact he (h ▸ List.mem_map.mpr ⟨t, ht, rfl⟩)
  simp [hn]

@[simp] theorem evaluate_compact (v : SparseField) (e : Edge) :
    evaluate (compact v) e = evaluate v e := by
  unfold compact evaluate
  rw [List.map_map]
  change ((v.map Prod.fst).dedup.map fun a => if e = a then evaluate v a else 0).sum = _
  rw [sum_unique_coordinates _ (List.nodup_dedup _) _ e]
  by_cases he : e ∈ v.map Prod.fst
  · simp only [List.mem_dedup, he, ite_true]
    rfl
  · simp only [List.mem_dedup, he, ite_false]
    exact (evaluate_eq_zero_of_not_mem v e he).symm

@[simp] theorem embed_compact (v : SparseField) : embed (compact v) = embed v := by
  ext e
  simp only [embed_apply, evaluate_compact]

theorem Supported.compact {v : SparseField} {R : ℕ} (hv : Supported v R) :
    Supported (compact v) R := by
  intro t ht j
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp ht
  have he' : e ∈ v.map Prod.fst := List.mem_dedup.mp he
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he'
  exact hv a ha j

/-- The count covers the whole containing lattice cube, including zeros. -/
theorem compact_length_bound {v : SparseField} {R : ℕ} (hv : Supported v R) :
    (compact v).length ≤ 3 * (2 * R + 1) ^ 3 := by
  have hsub : (v.map Prod.fst).toFinset ⊆
      Finset.univ ×ˢ Maxwell.Green.integerCube R := by
    intro e he
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp he)
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _,
      (Maxwell.Green.mem_integerCube R _).mpr (hv t ht)⟩
  have hc := Finset.card_le_card hsub
  simpa only [compact, List.length_map, ← List.card_toFinset,
    Finset.card_product, Finset.card_univ, Fintype.card_fin, Maxwell.Green.card_integerCube] using hc

/-- Horner evaluation of the geometric inverse sum, with exact
compaction after each iteration. -/
def hornerAction (m : Edge → ℚ) (z s : ℚ) : ℕ → SparseField → SparseField
  | 0, v => compact v
  | N + 1, v => compact (v ++ contractionStep m z s (hornerAction m z s N v))

def compactInverseAction (m : Edge → ℚ) (z s : ℚ) (N : ℕ) (v : SparseField) : SparseField :=
  compact (scale s (step m z (hornerAction m z s N v)))

theorem embed_hornerAction (m : Edge → ℚ) (K : ℝ) (hK : 0 ≤ K)
    (hm : ∀ e, |(m e : ℝ)| ≤ K) (z s : ℚ) (N : ℕ) (v : SparseField) :
    embed (hornerAction m z s N v) =
      (∑ j ∈ Finset.range (N + 1),
        ((1 : Field →L[ℂ] Field) - (s : ℂ) • operator m K hK hm z ^ 2) ^ j) (embed v) := by
  induction N with
  | zero => simp [hornerAction]
  | succ N ih =>
    rw [hornerAction, embed_compact, embed_append, embed_contractionStep m K hK hm, ih]
    rw [geom_sum_succ (n := N + 1)]
    change embed v + _ = _ + embed v
    exact add_comm _ _

theorem embed_compactInverseAction (m : Edge → ℚ) (K : ℝ) (hK : 0 ≤ K)
    (hm : ∀ e, |(m e : ℝ)| ≤ K) (z s : ℚ) (N : ℕ) (v : SparseField) :
    embed (compactInverseAction m z s N v) =
      inversePolynomial (operator m K hK hm z) (s : ℂ) N (embed v) := by
  rw [compactInverseAction, embed_compact, embed_scale, embed_step m K hK hm,
    embed_hornerAction m K hK hm]
  rfl

theorem Supported.hornerAction {v : SparseField} {R : ℕ} (hv : Supported v R)
    (m : Edge → ℚ) (z s : ℚ) (N : ℕ) :
    Supported (hornerAction m z s N v) (R + 4 * N) := by
  induction N with
  | zero => simpa only [FiniteStencil.hornerAction, Nat.mul_zero, Nat.add_zero] using hv.compact
  | succ N ih =>
    apply Supported.compact
    apply Supported.append (hv.mono (by omega))
    simpa only [Nat.mul_succ, Nat.add_assoc] using ih.contractionStep m z s

theorem hornerAction_length_bound {v : SparseField} {R : ℕ} (hv : Supported v R)
    (m : Edge → ℚ) (z s : ℚ) (N : ℕ) :
    (hornerAction m z s N v).length ≤ 3 * (2 * (R + 4 * N) + 1) ^ 3 := by
  cases N with
  | zero => simpa only [hornerAction, Nat.mul_zero, Nat.add_zero] using compact_length_bound hv
  | succ N =>
    apply compact_length_bound
    apply Supported.append (hv.mono (by omega))
    simpa only [Nat.mul_succ, Nat.add_assoc] using (hv.hornerAction m z s N).contractionStep m z s

theorem compactInverseAction_length_bound {v : SparseField} {R : ℕ} (hv : Supported v R)
    (m : Edge → ℚ) (z s : ℚ) (N : ℕ) :
    (compactInverseAction m z s N v).length ≤ 3 * (2 * (R + 4 * N + 2) + 1) ^ 3 :=
  compact_length_bound (((hv.hornerAction m z s N).step m z).scale s)

def compactCompression {ι : Type*} (basis : ι → SparseField) (m : Edge → ℚ)
    (z s : ℚ) (N : ℕ) : Matrix ι ι ℚ :=
  fun i j => pairing (basis i) (compactInverseAction m z s N (basis j))

theorem compactCompression_eq {ι : Type*} (basis : ι → SparseField) (m : Edge → ℚ)
    (K : ℝ) (hK : 0 ≤ K) (hm : ∀ e, |(m e : ℝ)| ≤ K) (z s : ℚ) (N : ℕ) :
    compactCompression basis m z s N = compression basis m z s N := by
  ext i j
  apply Rat.cast_injective (α := ℂ)
  rw [compactCompression, pairing_inner, embed_compactInverseAction m K hK hm,
    compression_entry m K hK hm]

end Maxwell.Defect.FiniteStencil
