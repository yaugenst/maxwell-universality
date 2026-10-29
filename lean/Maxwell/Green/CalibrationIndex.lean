import Maxwell.Green.CalibrationInteger
import Mathlib.Logic.Equiv.Fin.Basic

/-! Mixed-radix indexing of the finite stencil cube. Generation uses only
natural division/remainder and integer shifts; no ordered-set enumeration
or sorting is part of the algorithm. -/
namespace Maxwell.Defect.FiniteStencil
open Spectral Spectral.Lattice
set_option maxHeartbeats 600000

abbrev cubeWidth (R : ℕ) : ℕ := 2 * R + 1

/-- Three spatial digits and one edge-direction digit. -/
def radixCubeEquiv (R : ℕ) :
    (Fin 3 × (Fin (cubeWidth R) × (Fin (cubeWidth R) × Fin (cubeWidth R)))) ≃
      Fin (3 * cubeWidth R ^ 3) :=
  (Equiv.prodCongr (Equiv.refl (Fin 3))
    ((Equiv.prodCongr (Equiv.refl (Fin (cubeWidth R))) finProdFinEquiv).trans
      finProdFinEquiv)).trans
    (finProdFinEquiv.trans (finCongr (by ring)))

def radixEdge (R : ℕ) (i : Fin (3 * cubeWidth R ^ 3)) : Edge :=
  let digits := (radixCubeEquiv R).symm i
  (digits.1, ![(digits.2.1.val : ℤ) - R,
    (digits.2.2.1.val : ℤ) - R, (digits.2.2.2.val : ℤ) - R])

theorem radixEdge_injective (R : ℕ) : Function.Injective (radixEdge R) := by
  intro i j h
  apply (radixCubeEquiv R).symm.injective
  apply Prod.ext
  · exact congrArg (fun e : Edge => e.1) h
  · apply Prod.ext
    · apply Fin.ext
      have hx := congrArg (fun e : Edge => e.2 0) h
      simp only [radixEdge, Matrix.cons_val_zero] at hx
      omega
    · apply Prod.ext
      · apply Fin.ext
        have hx := congrArg (fun e : Edge => e.2 1) h
        simp only [radixEdge, Matrix.cons_val_one, Matrix.cons_val_zero] at hx
        omega
      · apply Fin.ext
        have hx := congrArg (fun e : Edge => e.2 2) h
        change (((radixCubeEquiv R).symm i).2.2.2.val : ℤ) - R =
          (((radixCubeEquiv R).symm j).2.2.2.val : ℤ) - R at hx
        omega

/-- Explicit index-to-edge embedding, using mixed-radix arithmetic. -/
def radixCubeEmbedding (R : ℕ) : Fin (3 * cubeWidth R ^ 3) ↪ Edge :=
  ⟨radixEdge R, radixEdge_injective R⟩

@[simp] theorem radixEdge_direction (R : ℕ) (i : Fin (3 * cubeWidth R ^ 3)) :
    (radixEdge R i).1.val = i.val / (cubeWidth R * (cubeWidth R * cubeWidth R)) := rfl

@[simp] theorem radixEdge_coordinate_zero (R : ℕ) (i : Fin (3 * cubeWidth R ^ 3)) :
    (radixEdge R i).2 0 =
      ((i.val % (cubeWidth R * (cubeWidth R * cubeWidth R)) /
        (cubeWidth R * cubeWidth R) : ℕ) : ℤ) - R := rfl

@[simp] theorem radixEdge_coordinate_one (R : ℕ) (i : Fin (3 * cubeWidth R ^ 3)) :
    (radixEdge R i).2 1 =
      ((i.val % (cubeWidth R * (cubeWidth R * cubeWidth R)) %
        (cubeWidth R * cubeWidth R) / cubeWidth R : ℕ) : ℤ) - R := rfl

@[simp] theorem radixEdge_coordinate_two (R : ℕ) (i : Fin (3 * cubeWidth R ^ 3)) :
    (radixEdge R i).2 2 =
      ((i.val % (cubeWidth R * (cubeWidth R * cubeWidth R)) %
        (cubeWidth R * cubeWidth R) % cubeWidth R : ℕ) : ℤ) - R := rfl

private theorem digit_bound (R : ℕ) (a : Fin (cubeWidth R)) :
    |(a.val : ℤ) - R| ≤ (R : ℤ) := by
  have h := a.isLt
  unfold cubeWidth at h
  rw [abs_le]
  constructor <;> omega

theorem radixEdge_bound (R : ℕ) (i : Fin (3 * cubeWidth R ^ 3)) (j : Direction) :
    |(radixEdge R i).2 j| ≤ (R : ℤ) := by
  fin_cases j
  · exact digit_bound R ((radixCubeEquiv R).symm i).2.1
  · exact digit_bound R ((radixCubeEquiv R).symm i).2.2.1
  · exact digit_bound R ((radixCubeEquiv R).symm i).2.2.2

private def siteDigit (R : ℕ) (a : ℤ) (ha : |a| ≤ (R : ℤ)) : Fin (cubeWidth R) :=
  ⟨(a + R).toNat, by obtain ⟨hlo, hhi⟩ := abs_le.mp ha; unfold cubeWidth; omega⟩

private theorem siteDigit_value (R : ℕ) (a : ℤ) (ha : |a| ≤ (R : ℤ)) :
    ((siteDigit R a ha).val : ℤ) - R = a := by
  have hlo := (abs_le.mp ha).1
  dsimp [siteDigit]
  omega

theorem range_radixCubeEmbedding (R : ℕ) :
    Set.range (radixCubeEmbedding R) = (cubeEdges R : Set Edge) := by
  ext e
  constructor
  · rintro ⟨i, rfl⟩
    apply Finset.mem_product.mpr
    exact ⟨Finset.mem_univ _, (Maxwell.Green.mem_integerCube R _).mpr (radixEdge_bound R i)⟩
  · intro he
    have hz := (Maxwell.Green.mem_integerCube R e.2).mp (Finset.mem_product.mp he).2
    let digits := (e.1, (siteDigit R (e.2 0) (hz 0),
      (siteDigit R (e.2 1) (hz 1), siteDigit R (e.2 2) (hz 2))))
    refine ⟨radixCubeEquiv R digits, ?_⟩
    change radixEdge R (radixCubeEquiv R digits) = e
    simp only [radixEdge, Equiv.symm_apply_apply]
    apply Prod.ext
    · rfl
    · funext j
      fin_cases j
      · exact siteDigit_value R (e.2 0) (hz 0)
      · exact siteDigit_value R (e.2 1) (hz 1)
      · exact siteDigit_value R (e.2 2) (hz 2)

theorem radixCubeEmbedding_covers (R : ℕ) : Covers (radixCubeEmbedding R) R := by
  intro e he
  rw [range_radixCubeEmbedding]
  exact Finset.mem_product.mpr ⟨Finset.mem_univ _, (Maxwell.Green.mem_integerCube R _).mpr he⟩

theorem radixCubeEmbedding_coordinate_bits (R : ℕ) (i : Fin (3 * cubeWidth R ^ 3))
    (j : Direction) : ((radixCubeEmbedding R i).2 j).natAbs.size ≤ R.size := by
  have h : (((radixCubeEmbedding R i).2 j).natAbs : ℤ) ≤ (R : ℤ) := by
    rw [Int.natCast_natAbs]
    exact radixEdge_bound R i j
  exact Nat.size_le_size (by exact_mod_cast h)

/-- The actual stencil is an explicit list of eighteen weighted edges. -/
def stencilTerms (m : Edge → ℚ) (z : ℚ) (e : Edge) : SparseField := step m z [(e, 1)]

theorem stencilTerms_length (m : Edge → ℚ) (z : ℚ) (e : Edge) :
    (stencilTerms m z e).length = 18 := by
  simpa only [stencilTerms, List.length_singleton, Nat.mul_one] using step_length m z [(e, 1)]

/-- The matrix generator performs exactly eighteen equality tests and a
rational sum. Repeated edges are deliberately retained in this fixed list. -/
theorem stencilMatrix_entry_terms {n : ℕ} (edges : Fin n → Edge) (m : Edge → ℚ)
    (z : ℚ) (i j : Fin n) :
    stencilMatrix edges m z i j =
      ((stencilTerms m z (edges j)).map fun t => if edges i = t.1 then t.2 else 0).sum := rfl

/-- The sixteen curl-curl terms are entirely independent of material. -/
def freeStencilTerms (e : Edge) : SparseField := curlAdjoint (curl [(e, 1)])

theorem freeStencilTerms_length (e : Edge) : (freeStencilTerms e).length = 16 := by
  simp only [freeStencilTerms, curlAdjoint_length, curl_length, List.length_singleton]

/-- Only one material lookup is needed per generated column; the remaining
terms are the fixed curl-curl stencil and the operating shift. -/
theorem stencilTerms_eq (m : Edge → ℚ) (z : ℚ) (e : Edge) :
    stencilTerms m z e = freeStencilTerms e ++ [(e, -(m e) / 64), (e, -z)] := by
  simp only [stencilTerms, step, freeStencilTerms, multiply, scale, List.map_cons,
    List.map_nil, mul_one, List.append_assoc, List.cons_append, List.nil_append]
  congr 3
  ring

theorem stencilMatrix_entry_formula {n : ℕ} (edges : Fin n → Edge) (m : Edge → ℚ)
    (z : ℚ) (i j : Fin n) :
    stencilMatrix edges m z i j = evaluate (freeStencilTerms (edges j)) (edges i) -
      (if edges i = edges j then m (edges j) / 64 + z else 0) := by
  change evaluate (stencilTerms m z (edges j)) (edges i) = _
  rw [stencilTerms_eq, evaluate_append]
  simp only [evaluate, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  split_ifs <;> ring

/-- Direct inverse address formula, obtained by shifting each coordinate to
a nonnegative radix digit. -/
def radixIndex (R : ℕ) (e : Edge) (he : ∀ j, |e.2 j| ≤ (R : ℤ)) :
    Fin (3 * cubeWidth R ^ 3) :=
  radixCubeEquiv R (e.1, (siteDigit R (e.2 0) (he 0),
    (siteDigit R (e.2 1) (he 1), siteDigit R (e.2 2) (he 2))))

@[simp] theorem radixIndex_val (R : ℕ) (e : Edge) (he : ∀ j, |e.2 j| ≤ (R : ℤ)) :
    (radixIndex R e he).val =
      ((e.2 2 + R).toNat + cubeWidth R * (e.2 1 + R).toNat) +
        (cubeWidth R * cubeWidth R) * (e.2 0 + R).toNat +
          (cubeWidth R * (cubeWidth R * cubeWidth R)) * e.1.val := rfl

theorem radixEdge_radixIndex (R : ℕ) (e : Edge) (he : ∀ j, |e.2 j| ≤ (R : ℤ)) :
    radixEdge R (radixIndex R e he) = e := by
  simp only [radixEdge, radixIndex, Equiv.symm_apply_apply]
  apply Prod.ext
  · rfl
  · funext j
    fin_cases j
    · exact siteDigit_value R (e.2 0) (he 0)
    · exact siteDigit_value R (e.2 1) (he 1)
    · exact siteDigit_value R (e.2 2) (he 2)

theorem radixIndex_radixEdge (R : ℕ) (i : Fin (3 * cubeWidth R ^ 3)) :
    radixIndex R (radixEdge R i) (radixEdge_bound R i) = i := by
  apply radixEdge_injective R
  exact radixEdge_radixIndex R (radixEdge R i) (radixEdge_bound R i)

/-- Cube addresses have logarithmic bit length in the coordinate radius. -/
theorem radixIndex_bits (R : ℕ) (i : Fin (3 * cubeWidth R ^ 3)) :
    i.val.size ≤ 2 + 3 * (cubeWidth R).size := by
  apply (Nat.size_le_size i.isLt.le).trans
  have h := Cost.CalibrationMatrix.size_mul_pow_bound 3 (cubeWidth R) 3
  have hthree : Nat.size 3 = 2 := by decide
  simpa only [hthree, Nat.mul_comm] using h

end Maxwell.Defect.FiniteStencil
