import Maxwell.Spectral.Lattice
import Maxwell.Defect.InversePolynomial
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Lean.Elab.Tactic.Omega

/-! Exact finite rational execution of the infinite Yee stencil.

A sparse field is a finite list of rational weighted lattice edges. Repeated
edges are allowed and summed; no support-detection or infinite inverse oracle
enters execution. The interpretation in the actual complex Hilbert space is
used only to prove that these finite operations compute the stated operator.
-/

namespace Maxwell.Defect.FiniteStencil

open Spectral Spectral.Lattice

abbrev SparseField := List (Edge × ℚ)

def scale (q : ℚ) (v : SparseField) : SparseField :=
  v.map fun t => (t.1, q * t.2)

def pullback (e : Equiv.Perm Edge) (v : SparseField) : SparseField :=
  v.map fun t => (e.symm t.1, t.2)

def multiply (m : Edge → ℚ) (v : SparseField) : SparseField :=
  v.map fun t => (t.1, m t.1 * t.2)

def evaluate (v : SparseField) (e : Edge) : ℚ :=
  (v.map fun t => if e = t.1 then t.2 else 0).sum

def curl (v : SparseField) : SparseField :=
  pullback (fieldPermutation directionCycle.symm (fun d => unitSite (d + 1))) v ++
  scale (-1) (pullback (fieldPermutation directionCycle.symm (fun _ => 0)) v) ++
  scale (-1) (pullback (fieldPermutation directionCycle (fun d => unitSite (d + 2))) v) ++
  pullback (fieldPermutation directionCycle (fun _ => 0)) v

def curlAdjoint (v : SparseField) : SparseField :=
  pullback (fieldPermutation directionCycle.symm (fun d => unitSite (d + 1))).symm v ++
  scale (-1) (pullback (fieldPermutation directionCycle.symm (fun _ => 0)).symm v) ++
  scale (-1) (pullback (fieldPermutation directionCycle (fun d => unitSite (d + 2))).symm v) ++
  pullback (fieldPermutation directionCycle (fun _ => 0)).symm v

/-- The electric operator with a rational operating shift `z`. -/
def step (m : Edge → ℚ) (z : ℚ) (v : SparseField) : SparseField :=
  curlAdjoint (curl v) ++ scale (-(1 / 64)) (multiply m v) ++ scale (-z) v

noncomputable def embed (v : SparseField) : Field :=
  (v.map fun t => lp.single 2 t.1 (t.2 : ℂ)).sum

@[simp] theorem embed_nil : embed [] = 0 := rfl

@[simp] theorem embed_cons (t : Edge × ℚ) (v : SparseField) :
    embed (t :: v) = lp.single 2 t.1 (t.2 : ℂ) + embed v := rfl

@[simp] theorem embed_append (u v : SparseField) : embed (u ++ v) = embed u + embed v := by
  simp [embed]

theorem embed_apply (v : SparseField) (e : Edge) : embed v e = (evaluate v e : ℂ) := by
  induction v with
  | nil => simp [embed, evaluate]
  | cons t v ih =>
      simp only [embed_cons, lp.coeFn_add, Pi.add_apply, ih, evaluate, List.map_cons,
        List.sum_cons, Rat.cast_add]
      congr 1
      by_cases h : e = t.1 <;> simp [lp.single_apply, h]

theorem embed_scale (q : ℚ) (v : SparseField) :
    embed (scale q v) = (q : ℂ) • embed v := by
  induction v with
  | nil => simp [scale]
  | cons t v ih =>
      simp only [scale, List.map_cons, embed_cons] at ⊢
      change lp.single 2 t.1 ((q * t.2 : ℚ) : ℂ) + embed (scale q v) = _
      rw [ih, smul_add, Rat.cast_mul]
      congr 1
      exact lp.single_smul (E := fun _ : Edge => ℂ) 2 t.1 (q : ℂ) (t.2 : ℂ)

theorem fieldPullback_single (p : Equiv.Perm Edge) (e : Edge) (z : ℂ) :
    fieldPullback p (lp.single 2 e z) = lp.single 2 (p.symm e) z := by
  ext i
  simp [fieldPullback_apply, lp.single_apply, Pi.single_apply, ← Equiv.eq_symm_apply]

theorem embed_pullback (p : Equiv.Perm Edge) (v : SparseField) :
    embed (pullback p v) = fieldPullback p (embed v) := by
  induction v with
  | nil => simp [pullback]
  | cons t v ih =>
      change lp.single 2 (p.symm t.1) (t.2 : ℂ) + embed (pullback p v) = _
      rw [ih, embed_cons, map_add, fieldPullback_single]

theorem fieldPullback_adjoint (p : Equiv.Perm Edge) :
    (fieldPullback p).adjoint = fieldPullback p.symm := by
  have h := (sequenceReindex p).adjoint_eq_symm
  change (fieldPullback p).adjoint = _ at h
  rw [h]
  rfl

theorem embed_curl (v : SparseField) : embed (curl v) = yeeCurl (embed v) := by
  simp only [curl, embed_append, embed_scale, embed_pullback, yeeCurl,
    add_apply, sub_apply]
  norm_num
  abel

theorem embed_curlAdjoint (v : SparseField) :
    embed (curlAdjoint v) = yeeCurl.adjoint (embed v) := by
  simp only [curlAdjoint, embed_append, embed_scale, embed_pullback, yeeCurl,
    map_add, map_sub, fieldPullback_adjoint, add_apply, sub_apply]
  norm_num
  abel

theorem embed_multiply (m : Edge → ℚ) (K : ℝ) (hK : 0 ≤ K)
    (hm : ∀ e, |(m e : ℝ)| ≤ K) (v : SparseField) :
    embed (multiply m v) = realSequenceMultiplier (fun e => (m e : ℝ)) K hK hm (embed v) := by
  ext e
  induction v with
  | nil => simp [multiply]
  | cons t v ih =>
      simp only [multiply, List.map_cons, embed_cons, lp.coeFn_add, Pi.add_apply,
        realSequenceMultiplier_apply, mul_add] at *
      rw [ih]
      congr 1
      by_cases h : e = t.1
      · subst e
        simp [lp.single_apply, Rat.cast_mul]
      · simp [lp.single_apply, h]

noncomputable def operator (m : Edge → ℚ) (K : ℝ) (hK : 0 ≤ K)
    (hm : ∀ e, |(m e : ℝ)| ≤ K) (z : ℚ) : Field →L[ℂ] Field :=
  electricOperator (fun e => (m e : ℝ)) K hK hm -
    (z : ℂ) • ContinuousLinearMap.id ℂ Field

theorem embed_step (m : Edge → ℚ) (K : ℝ) (hK : 0 ≤ K)
    (hm : ∀ e, |(m e : ℝ)| ≤ K) (z : ℚ) (v : SparseField) :
    embed (step m z v) = operator m K hK hm z (embed v) := by
  simp only [step, embed_append, embed_scale, embed_curlAdjoint, embed_curl,
    embed_multiply m K hK hm, operator, electricOperator,
    sub_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
  norm_num
  abel

/-- One application of `I - s H²`, using only exact rational operations. -/
def contractionStep (m : Edge → ℚ) (z s : ℚ) (v : SparseField) : SparseField :=
  v ++ scale (-s) (step m z (step m z v))

def contractionPower (m : Edge → ℚ) (z s : ℚ) : ℕ → SparseField → SparseField
  | 0, v => v
  | n + 1, v => contractionStep m z s (contractionPower m z s n v)

def geometricAction (m : Edge → ℚ) (z s : ℚ) : ℕ → SparseField → SparseField
  | 0, v => v
  | n + 1, v => geometricAction m z s n v ++ contractionPower m z s (n + 1) v

/-- The executable finite inverse polynomial, of operator degree `2N+1`. -/
def inverseAction (m : Edge → ℚ) (z s : ℚ) (N : ℕ) (v : SparseField) : SparseField :=
  scale s (step m z (geometricAction m z s N v))

theorem embed_contractionStep (m : Edge → ℚ) (K : ℝ) (hK : 0 ≤ K)
    (hm : ∀ e, |(m e : ℝ)| ≤ K) (z s : ℚ) (v : SparseField) :
    embed (contractionStep m z s v) =
      ((1 : Field →L[ℂ] Field) - (s : ℂ) • operator m K hK hm z ^ 2) (embed v) := by
  rw [contractionStep, embed_append, embed_scale, embed_step m K hK hm,
    embed_step m K hK hm]
  change embed v + ((-s : ℚ) : ℂ) •
    operator m K hK hm z (operator m K hK hm z (embed v)) =
    embed v - (s : ℂ) • operator m K hK hm z (operator m K hK hm z (embed v))
  simp only [Rat.cast_neg, neg_smul, sub_eq_add_neg]

theorem embed_contractionPower (m : Edge → ℚ) (K : ℝ) (hK : 0 ≤ K)
    (hm : ∀ e, |(m e : ℝ)| ≤ K) (z s : ℚ) (n : ℕ) (v : SparseField) :
    embed (contractionPower m z s n v) =
      (((1 : Field →L[ℂ] Field) - (s : ℂ) • operator m K hK hm z ^ 2) ^ n) (embed v) := by
  induction n with
  | zero => simp [contractionPower]
  | succ n ih =>
      rw [contractionPower, embed_contractionStep m K hK hm, ih,
        pow_succ' ((1 : Field →L[ℂ] Field) - (s : ℂ) • operator m K hK hm z ^ 2) n]
      rfl

theorem embed_geometricAction (m : Edge → ℚ) (K : ℝ) (hK : 0 ≤ K)
    (hm : ∀ e, |(m e : ℝ)| ≤ K) (z s : ℚ) (N : ℕ) (v : SparseField) :
    embed (geometricAction m z s N v) =
      (∑ j ∈ Finset.range (N + 1),
        ((1 : Field →L[ℂ] Field) - (s : ℂ) • operator m K hK hm z ^ 2) ^ j)
        (embed v) := by
  induction N with
  | zero => simp [geometricAction]
  | succ N ih =>
      rw [geometricAction, embed_append, ih, embed_contractionPower m K hK hm]
      rw [Finset.sum_range_succ _ (N + 1)]
      rfl

/-- Exact semantic binding to the polynomial used in the inverse error bound. -/
theorem embed_inverseAction (m : Edge → ℚ) (K : ℝ) (hK : 0 ≤ K)
    (hm : ∀ e, |(m e : ℝ)| ≤ K) (z s : ℚ) (N : ℕ) (v : SparseField) :
    embed (inverseAction m z s N v) =
      inversePolynomial (operator m K hK hm z) (s : ℂ) N (embed v) := by
  rw [inverseAction, embed_scale, embed_step m K hK hm,
    embed_geometricAction m K hK hm]
  rfl

def pairing (u v : SparseField) : ℚ :=
  (u.map fun t => t.2 * evaluate v t.1).sum

theorem pairing_inner (u v : SparseField) :
    (pairing u v : ℂ) = inner ℂ (embed u) (embed v) := by
  induction u with
  | nil => simp [pairing]
  | cons t u ih =>
      simp only [pairing, List.map_cons, List.sum_cons, Rat.cast_add, Rat.cast_mul,
        embed_cons, inner_add_left, lp.inner_single_left, RCLike.inner_apply,
        embed_apply] at *
      simp [ih, mul_comm]

/-- A finite rational matrix, computable from the finitely supported defect
basis and the polynomial degree. -/
def compression {ι : Type*} (basis : ι → SparseField) (m : Edge → ℚ)
    (z s : ℚ) (N : ℕ) : Matrix ι ι ℚ :=
  fun i j => pairing (basis i) (inverseAction m z s N (basis j))

theorem compression_entry (m : Edge → ℚ) (K : ℝ) (hK : 0 ≤ K)
    (hm : ∀ e, |(m e : ℝ)| ≤ K) (z s : ℚ) (N : ℕ)
    {ι : Type*} (basis : ι → SparseField) (i j : ι) :
    (compression basis m z s N i j : ℂ) =
      inner ℂ (embed (basis i))
        (inversePolynomial (operator m K hK hm z) (s : ℂ) N (embed (basis j))) := by
  rw [compression, pairing_inner, embed_inverseAction m K hK hm]

/-- An explicit coordinate-box bound on every stored edge, including terms
which may cancel. This makes the propagation bound independent of cancellation. -/
def Supported (v : SparseField) (R : ℕ) : Prop :=
  ∀ t ∈ v, ∀ j : Direction, |t.1.2 j| ≤ (R : ℤ)

theorem Supported.mono {v : SparseField} {R S : ℕ} (hv : Supported v R) (hRS : R ≤ S) :
    Supported v S := by
  intro t ht j
  exact (hv t ht j).trans (by exact_mod_cast hRS)

theorem Supported.append {u v : SparseField} {R : ℕ}
    (hu : Supported u R) (hv : Supported v R) : Supported (u ++ v) R := by
  intro t ht j
  rcases List.mem_append.mp ht with h | h
  · exact hu t h j
  · exact hv t h j

theorem Supported.scale {v : SparseField} {R : ℕ} (hv : Supported v R) (q : ℚ) :
    Supported (scale q v) R := by
  intro t ht j
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ht
  exact hv a ha j

theorem Supported.multiply {v : SparseField} {R : ℕ} (hv : Supported v R) (m : Edge → ℚ) :
    Supported (multiply m v) R := by
  intro t ht j
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ht
  exact hv a ha j

theorem Supported.permutation {v : SparseField} {R D : ℕ} (hv : Supported v R)
    (p : Equiv.Perm Direction) (w : Direction → Site)
    (hw : ∀ d j, |w d j| ≤ (D : ℤ)) :
    Supported (pullback (fieldPermutation p w) v) (R + D) := by
  intro t ht j
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ht
  change |a.1.2 j - w (p.symm a.1.1) j| ≤ ((R + D : ℕ) : ℤ)
  calc
    _ ≤ |a.1.2 j| + |w (p.symm a.1.1) j| := abs_sub _ _
    _ ≤ (R : ℤ) + D := add_le_add (hv a ha j) (hw _ j)
    _ = _ := by norm_cast

theorem Supported.permutation_inverse {v : SparseField} {R D : ℕ} (hv : Supported v R)
    (p : Equiv.Perm Direction) (w : Direction → Site)
    (hw : ∀ d j, |w d j| ≤ (D : ℤ)) :
    Supported (pullback (fieldPermutation p w).symm v) (R + D) := by
  intro t ht j
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ht
  change |a.1.2 j + w a.1.1 j| ≤ ((R + D : ℕ) : ℤ)
  calc
    _ ≤ |a.1.2 j| + |w a.1.1 j| := abs_add_le _ _
    _ ≤ (R : ℤ) + D := add_le_add (hv a ha j) (hw _ j)
    _ = _ := by norm_cast

theorem unitSite_bound (d j : Direction) : |unitSite d j| ≤ (1 : ℤ) := by
  by_cases h : j = d <;> simp [unitSite, h]

theorem Supported.curl {v : SparseField} {R : ℕ} (hv : Supported v R) :
    Supported (curl v) (R + 1) := by
  have h0 := hv.permutation directionCycle.symm (fun d => unitSite (d + 1))
    (fun d j => unitSite_bound (d + 1) j)
  have h1 := hv.permutation (D := 1) directionCycle.symm (fun _ => 0) (by simp)
  have h2 := hv.permutation directionCycle (fun d => unitSite (d + 2))
    (fun d j => unitSite_bound (d + 2) j)
  have h3 := hv.permutation (D := 1) directionCycle (fun _ => 0) (by simp)
  exact ((h0.append (h1.scale (-1))).append (h2.scale (-1))).append h3

theorem Supported.curlAdjoint {v : SparseField} {R : ℕ} (hv : Supported v R) :
    Supported (curlAdjoint v) (R + 1) := by
  have h0 := hv.permutation_inverse directionCycle.symm (fun d => unitSite (d + 1))
    (fun d j => unitSite_bound (d + 1) j)
  have h1 := hv.permutation_inverse (D := 1) directionCycle.symm (fun _ => 0) (by simp)
  have h2 := hv.permutation_inverse directionCycle (fun d => unitSite (d + 2))
    (fun d j => unitSite_bound (d + 2) j)
  have h3 := hv.permutation_inverse (D := 1) directionCycle (fun _ => 0) (by simp)
  exact ((h0.append (h1.scale (-1))).append (h2.scale (-1))).append h3

theorem Supported.step {v : SparseField} {R : ℕ} (hv : Supported v R)
    (m : Edge → ℚ) (z : ℚ) : Supported (step m z v) (R + 2) := by
  have hc : Supported (FiniteStencil.curlAdjoint (FiniteStencil.curl v)) (R + 2) := by
    simpa [Nat.add_assoc] using hv.curl.curlAdjoint
  exact (hc.append (((hv.multiply m).scale (-(1 / 64))).mono (by omega))).append
    ((hv.scale (-z)).mono (by omega))

theorem Supported.contractionStep {v : SparseField} {R : ℕ} (hv : Supported v R)
    (m : Edge → ℚ) (z s : ℚ) : Supported (contractionStep m z s v) (R + 4) := by
  have hh : Supported (FiniteStencil.step m z (FiniteStencil.step m z v)) (R + 4) := by
    simpa [Nat.add_assoc] using (hv.step m z).step m z
  exact (hv.mono (by omega)).append (hh.scale (-s))

theorem Supported.contractionPower {v : SparseField} {R : ℕ} (hv : Supported v R)
    (m : Edge → ℚ) (z s : ℚ) (n : ℕ) :
    Supported (contractionPower m z s n v) (R + 4 * n) := by
  induction n with
  | zero => simpa [FiniteStencil.contractionPower] using hv
  | succ n ih =>
      simpa only [FiniteStencil.contractionPower, Nat.mul_succ, Nat.add_assoc] using
        ih.contractionStep m z s

theorem Supported.geometricAction {v : SparseField} {R : ℕ} (hv : Supported v R)
    (m : Edge → ℚ) (z s : ℚ) (N : ℕ) :
    Supported (geometricAction m z s N v) (R + 4 * N) := by
  induction N with
  | zero => simpa [FiniteStencil.geometricAction] using hv
  | succ N ih =>
      exact (ih.mono (by omega)).append (hv.contractionPower m z s (N + 1))

/-- Degree `2N+1` requires only the input box enlarged by `4N+2` sites. -/
theorem Supported.inverseAction {v : SparseField} {R : ℕ} (hv : Supported v R)
    (m : Edge → ℚ) (z s : ℚ) (N : ℕ) :
    Supported (inverseAction m z s N v) (R + 4 * N + 2) :=
  ((hv.geometricAction m z s N).step m z).scale s

theorem curl_length (v : SparseField) : (curl v).length = 4 * v.length := by
  simp [curl, pullback, scale]
  omega

theorem curlAdjoint_length (v : SparseField) : (curlAdjoint v).length = 4 * v.length := by
  simp [curlAdjoint, pullback, scale]
  omega

theorem step_length (m : Edge → ℚ) (z : ℚ) (v : SparseField) :
    (step m z v).length = 18 * v.length := by
  simp only [step, List.length_append, curlAdjoint_length, curl_length,
    scale, multiply, List.length_map]
  omega

theorem contractionPower_length (m : Edge → ℚ) (z s : ℚ) (n : ℕ) (v : SparseField) :
    (contractionPower m z s n v).length = 325 ^ n * v.length := by
  induction n with
  | zero => simp [contractionPower]
  | succ n ih =>
      simp only [contractionPower, contractionStep, List.length_append,
        scale, List.length_map, step_length, ih, pow_succ]
      ring

theorem geometricAction_length (m : Edge → ℚ) (z s : ℚ) (N : ℕ) (v : SparseField) :
    (geometricAction m z s N v).length =
      (∑ j ∈ Finset.range (N + 1), 325 ^ j) * v.length := by
  induction N with
  | zero => simp [geometricAction]
  | succ N ih =>
      rw [geometricAction, List.length_append, ih, contractionPower_length,
        Finset.sum_range_succ _ (N + 1), add_mul]

theorem inverseAction_length (m : Edge → ℚ) (z s : ℚ) (N : ℕ) (v : SparseField) :
    (inverseAction m z s N v).length =
      18 * (∑ j ∈ Finset.range (N + 1), 325 ^ j) * v.length := by
  simp only [inverseAction, scale, List.length_map, step_length, geometricAction_length]
  ring

def coordinateBasis {ι : Type*} (edges : ι → Edge) (i : ι) : SparseField := [(edges i, 1)]

theorem embed_coordinateBasis {ι : Type*} (edges : ι → Edge) (i : ι) :
    embed (coordinateBasis edges i) = lp.single 2 (edges i) (1 : ℂ) := by
  simp [coordinateBasis]

theorem coordinate_compression_entry (m : Edge → ℚ) (K : ℝ) (hK : 0 ≤ K)
    (hm : ∀ e, |(m e : ℝ)| ≤ K) (z s : ℚ) (N : ℕ)
    {ι : Type*} (edges : ι → Edge) (i j : ι) :
    (compression (coordinateBasis edges) m z s N i j : ℂ) =
      inversePolynomial (operator m K hK hm z) (s : ℂ) N
        (lp.single 2 (edges j) (1 : ℂ)) (edges i) := by
  rw [compression_entry m K hK hm, embed_coordinateBasis, embed_coordinateBasis]
  simp only [lp.inner_single_left, RCLike.inner_apply, map_one, mul_one]

theorem operator_selfAdjoint (m : Edge → ℚ) (K : ℝ) (hK : 0 ≤ K)
    (hm : ∀ e, |(m e : ℝ)| ≤ K) (z : ℚ) :
    IsSelfAdjoint (operator m K hK hm z) := by
  unfold operator
  apply IsSelfAdjoint.sub (R := Field →L[ℂ] Field)
    (electricOperator_selfAdjoint (fun e => (m e : ℝ)) K hK hm)
  apply (show IsSelfAdjoint (z : ℂ) by simp [IsSelfAdjoint]).smul
  change IsSelfAdjoint (1 : Field →L[ℂ] Field)
  simp [IsSelfAdjoint]

/-- The exact rational output is symmetric, not merely close to a symmetric
matrix. The proof uses the actual self-adjoint lattice operator. -/
theorem compression_symmetric (m : Edge → ℚ) (K : ℝ) (hK : 0 ≤ K)
    (hm : ∀ e, |(m e : ℝ)| ≤ K) (z s : ℚ) (N : ℕ)
    {ι : Type*} (basis : ι → SparseField) :
    (compression basis m z s N).transpose = compression basis m z s N := by
  have hP := inversePolynomial_selfAdjoint (operator m K hK hm z) (s : ℂ) N
    (operator_selfAdjoint m K hK hm z) (by simp [IsSelfAdjoint])
  have hsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hP
  ext i j
  have hij := hsym (embed (basis i)) (embed (basis j))
  have hij' : (compression basis m z s N j i : ℂ) =
      (compression basis m z s N i j : ℂ) := by
    rw [← star_ratCast (compression basis m z s N j i),
      compression_entry m K hK hm]
    change starRingEnd ℂ (inner ℂ (embed (basis j))
      (inversePolynomial (operator m K hK hm z) (s : ℂ) N (embed (basis i)))) = _
    rw [inner_conj_symm]
    exact hij.trans (compression_entry m K hK hm z s N basis i j).symm
  exact_mod_cast hij'

end Maxwell.Defect.FiniteStencil
