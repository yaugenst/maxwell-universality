import Maxwell.Certificate.FourierBinding
import Maxwell.Certificate.Coverage
import Mathlib.Algebra.Order.ToIntervalMod

/-! A constructive FCC reciprocal Voronoi representative and the finite
sorting network reducing its absolute coordinates to the certified wedge. -/

noncomputable section
namespace Maxwell.Spectral.ReciprocalCover
open Maxwell.Certificate Maxwell.Certificate.FourierBinding
open PrimitiveYee
open PeriodicYee (Momentum Direction)

def reciprocalShift (n : Translation) : Momentum :=
  ![(n 0 : ℝ), (2*n 1-n 0 : ℤ), (2*n 2-n 0 : ℤ)]

theorem reciprocalShift_add (n m : Translation) :
    reciprocalShift (n+m) = reciprocalShift n + reciprocalShift m := by
  ext j
  fin_cases j <;> simp [reciprocalShift] <;> ring

theorem boundaryMomentum_reciprocalShift (c : Momentum) (n : Translation) :
    boundaryMomentum (c + reciprocalShift n) =
      fun j => boundaryMomentum c j + 2*Real.pi*(n j : ℝ) := by
  ext j
  fin_cases j <;> simp [boundaryMomentum, reciprocalShift] <;> ring

/-- Actual primitive characters, and hence the boundary-gauge matrices,
are periodic under every integer reciprocal translation. -/
theorem character_integer_periodic (k : Momentum) (n t : Translation) :
    character (fun j => k j + 2*Real.pi*(n j : ℝ)) t = character k t := by
  unfold character
  have he : (∑ j : Direction, (k j + 2*Real.pi*(n j : ℝ))*(t j : ℝ)) =
      (∑ j, k j*(t j : ℝ)) + 2*Real.pi*((∑ j, n j*t j : ℤ) : ℝ) := by
    simp only [Fin.sum_univ_three]
    push_cast
    ring
  have hec := congrArg Complex.ofReal he
  push_cast at hec ⊢
  rw [hec, mul_add, Complex.exp_add]
  have hp : Complex.exp (Complex.I *
      (2*(Real.pi : ℂ)*((∑ j, n j*t j : ℤ) : ℂ))) = 1 := by
    convert Complex.exp_int_mul_two_pi_mul_I (∑ j, n j*t j) using 1
    congr 1
    ring
  push_cast at hp
  rw [hp, mul_one]

theorem curl_integer_periodic (k : Momentum) (n : Translation) :
    curl (fun j => k j + 2*Real.pi*(n j : ℝ)) = curl k := by
  have hd (j : Direction) : difference (fun i => k i+2*Real.pi*(n i : ℝ)) j = difference k j := by
    ext a b
    simp only [difference, boundaryPhase,
      character_integer_periodic]
  ext a b
  simp only [curl, hd]

theorem fiber_reciprocal_periodic (material : PeriodicYee.Cell20 → ℝ)
    (c : Momentum) (n : Translation) :
    fiber material (boundaryMomentum (c + reciprocalShift n)) =
      fiber material (boundaryMomentum c) := by
  rw [boundaryMomentum_reciprocalShift]
  simp only [fiber, curl_integer_periodic]

private def sign (x : ℝ) : ℤ := if 0 ≤ x then 1 else -1

private theorem sign_abs_shift (x : ℝ) (hx : |x| ≤ 1) :
    |x - (sign x : ℝ)| = 1-|x| := by
  unfold sign
  split_ifs with h
  · rw [Int.cast_one, abs_of_nonneg h, abs_of_nonpos (by linarith [(abs_le.mp hx).2])]
    ring
  · rw [Int.cast_neg, Int.cast_one, abs_of_neg (lt_of_not_ge h),
      abs_of_nonneg (by linarith [(abs_le.mp hx).1])]
    ring

private theorem sign_reciprocal (c : Momentum) :
    ∃ n : Translation, reciprocalShift n = fun j => (sign (c j) : ℝ) := by
  refine ⟨![sign (c 0), (sign (c 0)+sign (c 1))/2, (sign (c 0)+sign (c 2))/2], ?_⟩
  have h0 : sign (c 0) = 1 ∨ sign (c 0) = -1 := by unfold sign; split_ifs <;> simp
  have h1 : sign (c 1) = 1 ∨ sign (c 1) = -1 := by unfold sign; split_ifs <;> simp
  have h2 : sign (c 2) = 1 ∨ sign (c 2) = -1 := by unfold sign; split_ifs <;> simp
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
    ext j <;> fin_cases j <;> norm_num [reciprocalShift, h0, h1, h2]

/-- Every Cartesian momentum has an actual FCC reciprocal translate in
the closed truncated-octahedral Voronoi zone. -/
theorem exists_voronoi_representative (c : Momentum) :
    ∃ v : Momentum, (∀ j, |v j| ≤ 1) ∧ (∑ j, |v j|) ≤ 3/2 ∧
      ∃ n : Translation, c = v + reciprocalShift n := by
  let hp : (0 : ℝ) < 2 := by norm_num
  let u : Momentum := fun j => toIcoMod hp (-1) (c j)
  let a : Translation := fun j => toIcoDiv hp (-1) (c j)
  let n : Translation := ![2*a 0, a 0+a 1, a 0+a 2]
  have hu (j : Direction) : |u j| ≤ 1 := by
    have h := toIcoMod_mem_Ico hp (-1) (c j)
    exact abs_le.mpr ⟨h.1, by linarith [h.2]⟩
  have hn : c = u + reciprocalShift n := by
    ext j
    have h := toIcoMod_add_toIcoDiv_zsmul hp (-1) (c j)
    change u j + a j • (2 : ℝ) = c j at h
    rw [zsmul_eq_mul] at h
    rw [← h]
    fin_cases j <;> simp [n, reciprocalShift] <;> ring
  by_cases hsum : (∑ j, |u j|) ≤ 3/2
  · exact ⟨u, hu, hsum, n, hn⟩
  · obtain ⟨m, hm⟩ := sign_reciprocal u
    let v : Momentum := fun j => u j - (sign (u j) : ℝ)
    have hv (j : Direction) : |v j| = 1-|u j| := sign_abs_shift _ (hu j)
    refine ⟨v, ?_, ?_, n+m, ?_⟩
    · intro j
      rw [hv]
      linarith [abs_nonneg (u j)]
    · simp only [hv, Fin.sum_univ_three] at hsum ⊢
      linarith
    · rw [hn, reciprocalShift_add, hm]
      ext j
      simp only [Pi.add_apply, v]
      ring

def swap01 (c : Momentum) : Momentum := ![c 1,c 0,c 2]
def swap12 (c : Momentum) : Momentum := ![c 0,c 2,c 1]
def compare01 (c : Momentum) : Momentum := if c 0 < c 1 then swap01 c else c
def compare12 (c : Momentum) : Momentum := if c 1 < c 2 then swap12 c else c

def sort (c : Momentum) : Momentum := compare01 (compare12 (compare01 c))

theorem sort_order (c : Momentum) : (sort c) 2 ≤ (sort c) 1 ∧ (sort c) 1 ≤ (sort c) 0 := by
  unfold sort compare01 compare12
  split_ifs <;> simp_all [swap01, swap12] <;> (try constructor) <;> linarith

theorem sort_sum (c : Momentum) : ∑ j, sort c j = ∑ j, c j := by
  unfold sort compare01 compare12
  split_ifs <;> simp [swap01, swap12, Fin.sum_univ_three] <;> ring

theorem sort_bounds (c : Momentum) (a b : ℝ) (hc : ∀ j, a ≤ c j ∧ c j ≤ b) :
    ∀ j, a ≤ sort c j ∧ sort c j ≤ b := by
  have h01 (x : Momentum) (hx : ∀ j, a ≤ x j ∧ x j ≤ b) :
      ∀ j, a ≤ compare01 x j ∧ compare01 x j ≤ b := by
    intro j
    unfold compare01
    split_ifs
    · fin_cases j <;> simpa [swap01] using hx _
    · exact hx j
  have h12 (x : Momentum) (hx : ∀ j, a ≤ x j ∧ x j ≤ b) :
      ∀ j, a ≤ compare12 x j ∧ compare12 x j ≤ b := by
    intro j
    unfold compare12
    split_ifs
    · fin_cases j <;> simpa [swap12] using hx _
    · exact hx j
  exact h01 _ (h12 _ (h01 _ hc))

theorem sort_wedge (c : Momentum) (hc : (∑ j, c j) ≤ 3/2) : Box.Wedge (sort c) := by
  refine ⟨(sort_order c).1, (sort_order c).2, ?_⟩
  have h := sort_sum c
  simp only [Fin.sum_univ_three] at h hc
  linarith

/-- The finite three-comparator sorting network preserves any predicate
invariant under the two adjacent actual cubic generators. -/
theorem sort_invariant (P : Momentum → Prop)
    (h01 : ∀ x, P (swap01 x) ↔ P x) (h12 : ∀ x, P (swap12 x) ↔ P x) (c : Momentum) :
    P (sort c) ↔ P c := by
  have hc01 (x : Momentum) : P (compare01 x) ↔ P x := by
    unfold compare01
    split_ifs
    · exact h01 x
    · rfl
  have hc12 (x : Momentum) : P (compare12 x) ↔ P x := by
    unfold compare12
    split_ifs
    · exact h12 x
    · rfl
  exact (hc01 _).trans ((hc12 _).trans (hc01 _))

theorem sort_sum_map (f : ℝ → ℝ) (c : Momentum) :
    ∑ j, f (sort c j) = ∑ j, f (c j) := by
  unfold sort compare01 compare12
  split_ifs <;> simp [swap01, swap12, Fin.sum_univ_three] <;> ring

def flip (j : Direction) (c : Momentum) : Momentum := Function.update c j (-c j)

theorem flip_one (c : Momentum) : flip 1 c = swap01 (flip 0 (swap01 c)) := by
  ext j
  fin_cases j <;> simp [flip, swap01]

theorem flip_two (c : Momentum) : flip 2 c = swap12 (flip 1 (swap12 c)) := by
  ext j
  fin_cases j <;> simp [flip, swap12]

/-- Adjacent swaps and one coordinate reflection generate every sign change. -/
theorem flip_invariant (P : Momentum → Prop)
    (h01 : ∀ x, P (swap01 x) ↔ P x) (h12 : ∀ x, P (swap12 x) ↔ P x)
    (h0 : ∀ x, P (flip 0 x) ↔ P x) (j : Direction) (c : Momentum) :
    P (flip j c) ↔ P c := by
  have h1 (x : Momentum) : P (flip 1 x) ↔ P x := by
    rw [flip_one]
    exact (h01 _).trans ((h0 _).trans (h01 _))
  fin_cases j
  · exact h0 c
  · exact h1 c
  · change P (flip 2 c) ↔ P c
    rw [flip_two]
    exact (h12 _).trans ((h1 _).trans (h12 _))

/-- The absolute-coordinate reduction uses exactly the actual cubic generators. -/
theorem abs_invariant (P : Momentum → Prop)
    (h01 : ∀ x, P (swap01 x) ↔ P x) (h12 : ∀ x, P (swap12 x) ↔ P x)
    (h0 : ∀ x, P (flip 0 x) ↔ P x) (c : Momentum) :
    P (fun j => |c j|) ↔ P c := by
  have ha (j : Direction) (x : Momentum) : P (Function.update x j |x j|) ↔ P x := by
    by_cases hx : 0 ≤ x j
    · rw [abs_of_nonneg hx, Function.update_eq_self]
    · rw [abs_of_neg (lt_of_not_ge hx)]
      exact flip_invariant P h01 h12 h0 j x
  have he : (Function.update (Function.update (Function.update c 0 |c 0|) 1 |c 1|) 2 |c 2|) =
      fun j => |c j| := by
    ext j
    fin_cases j <;> simp
  rw [← he]
  have h2 : P (Function.update (Function.update (Function.update c 0 |c 0|) 1 |c 1|) 2 |c 2|) ↔
      P (Function.update (Function.update c 0 |c 0|) 1 |c 1|) := by
    simpa using ha 2 (Function.update (Function.update c 0 |c 0|) 1 |c 1|)
  have h1 : P (Function.update (Function.update c 0 |c 0|) 1 |c 1|) ↔
      P (Function.update c 0 |c 0|) := by
    simpa using ha 1 (Function.update c 0 |c 0|)
  exact h2.trans (h1.trans (ha 0 c))

/-- Undoing sorting and absolute values gives a ball around an actual signed
L point. No broken symmetry of the perturbed material is used in this statement. -/
theorem signed_local_ball (c : Momentum) (hc : Box.LocalBall (sort (fun j => |c j|))) :
    ∃ s : Translation, (∀ j, s j = 1 ∨ s j = -1) ∧
      (∑ j, (c j-(s j : ℝ)/2)^2) ≤ 1/400 := by
  refine ⟨fun j => sign (c j), ?_, ?_⟩
  · intro j
    change sign (c j) = 1 ∨ sign (c j) = -1
    unfold sign
    split_ifs <;> simp
  · have hs := sort_sum_map (fun x : ℝ => (x-1/2)^2) (fun j => |c j|)
    have he (j : Direction) : (c j-(sign (c j) : ℝ)/2)^2 = (|c j|-1/2)^2 := by
      unfold sign
      split_ifs with h
      · rw [Int.cast_one, abs_of_nonneg h]
      · rw [Int.cast_neg, Int.cast_one, abs_of_neg (lt_of_not_ge h)]
        ring
    simp only [he]
    rw [← hs]
    simpa only [Box.LocalBall, Fin.sum_univ_three] using hc

/-- A generator-invariant statement on the closed ordered wedge holds at
every momentum once actual reciprocal periodicity is supplied. -/
theorem of_wedge (P : Momentum → Prop)
    (hperiod : ∀ c n, P (c+reciprocalShift n) ↔ P c)
    (h01 : ∀ x, P (swap01 x) ↔ P x) (h12 : ∀ x, P (swap12 x) ↔ P x)
    (h0 : ∀ x, P (flip 0 x) ↔ P x)
    (hwedge : ∀ x, (∀ j, 0 ≤ x j ∧ x j ≤ 1) → Box.Wedge x → P x)
    (c : Momentum) : P c := by
  obtain ⟨v, hv, hs, n, hn⟩ := exists_voronoi_representative c
  have hb := sort_bounds (fun j => |v j|) 0 1 (fun j => ⟨abs_nonneg _, hv j⟩)
  have hw := sort_wedge (fun j => |v j|) hs
  have hp := hwedge _ hb hw
  have hvP := (abs_invariant P h01 h12 h0 v).mp
    ((sort_invariant P h01 h12 (fun j => |v j|)).mp hp)
  rw [hn]
  exact (hperiod v n).mpr hvP

end Maxwell.Spectral.ReciprocalCover
