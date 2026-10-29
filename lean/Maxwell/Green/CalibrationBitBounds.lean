import Maxwell.Green.CalibrationPrecision
import Maxwell.Defect.ConcreteFiniteStencil
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.Size

/-! Exact storage bounds for the compact rational inverse iteration. -/
namespace Maxwell.Defect.FiniteStencil
open Spectral Spectral.Lattice
set_option maxHeartbeats 600000

/-- One common denominator clears every stored coefficient. -/
def HasDenominator (v : SparseField) (D : ℕ) : Prop :=
  ∀ t ∈ v, t.2.den ∣ D

theorem HasDenominator.mono {v : SparseField} {D E : ℕ}
    (h : HasDenominator v D) (hDE : D ∣ E) : HasDenominator v E :=
  fun t ht => (h t ht).trans hDE

theorem HasDenominator.append {u v : SparseField} {D : ℕ}
    (hu : HasDenominator u D) (hv : HasDenominator v D) : HasDenominator (u ++ v) D := by
  intro t ht
  rcases List.mem_append.mp ht with h | h
  · exact hu t h
  · exact hv t h

theorem HasDenominator.scale {v : SparseField} {D E : ℕ} (hv : HasDenominator v E)
    (q : ℚ) (hq : q.den ∣ D) : HasDenominator (scale q v) (D * E) := by
  intro t ht
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ht
  exact (Rat.mul_den_dvd q a.2).trans (Nat.mul_dvd_mul hq (hv a ha))

theorem HasDenominator.multiply {v : SparseField} {D E : ℕ} (hv : HasDenominator v E)
    (m : Edge → ℚ) (hm : ∀ e, (m e).den ∣ D) : HasDenominator (multiply m v) (D * E) := by
  intro t ht
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ht
  exact (Rat.mul_den_dvd (m a.1) a.2).trans (Nat.mul_dvd_mul (hm _) (hv a ha))

theorem HasDenominator.pullback {v : SparseField} {D : ℕ} (hv : HasDenominator v D)
    (p : Equiv.Perm Edge) : HasDenominator (pullback p v) D := by
  intro t ht
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ht
  exact hv a ha

private theorem sum_denominator (l : List ℚ) (D : ℕ) (h : ∀ q ∈ l, q.den ∣ D) :
    l.sum.den ∣ D := by
  induction l with
  | nil => simp
  | cons q l ih =>
    simp only [List.sum_cons]
    exact (Rat.add_den_dvd_lcm _ _).trans (Nat.lcm_dvd (h _ (by simp))
      (ih (fun a ha => h a (by simp [ha]))))

theorem HasDenominator.evaluate {v : SparseField} {D : ℕ} (hv : HasDenominator v D)
    (e : Edge) : (evaluate v e).den ∣ D := by
  apply sum_denominator
  intro q hq
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hq
  split_ifs
  · exact hv t ht
  · simp

theorem HasDenominator.compact {v : SparseField} {D : ℕ} (hv : HasDenominator v D) :
    HasDenominator (compact v) D := by
  intro t ht
  obtain ⟨e, _, rfl⟩ := List.mem_map.mp ht
  exact hv.evaluate e

private theorem HasDenominator.negate {v : SparseField} {D : ℕ}
    (hv : HasDenominator v D) : HasDenominator (FiniteStencil.scale (-1) v) D := by
  simpa using hv.scale (-1) (by simp : (-1 : ℚ).den ∣ 1)

theorem HasDenominator.curl {v : SparseField} {D : ℕ} (hv : HasDenominator v D) :
    HasDenominator (curl v) D :=
  (((hv.pullback _).append (hv.pullback _).negate).append
    (hv.pullback _).negate).append (hv.pullback _)

theorem HasDenominator.curlAdjoint {v : SparseField} {D : ℕ} (hv : HasDenominator v D) :
    HasDenominator (curlAdjoint v) D :=
  (((hv.pullback _).append (hv.pullback _).negate).append
    (hv.pullback _).negate).append (hv.pullback _)

/-- A fixed denominator for all stencil constants. Squaring the denominator
per stencil application also covers the factor `1/64`. -/
theorem HasDenominator.step {v : SparseField} {D E : ℕ} (hv : HasDenominator v E)
    (m : Edge → ℚ) (z : ℚ) (h64 : 64 ∣ D) (hm : ∀ e, (m e).den ∣ D)
    (hz : z.den ∣ D) : HasDenominator (step m z v) (D ^ 2 * E) := by
  apply HasDenominator.append
  · apply HasDenominator.append
    · exact hv.curl.curlAdjoint.mono (dvd_mul_left _ _)
    · have h := (hv.multiply m hm).scale (-(1 / 64))
        (by norm_num; exact h64)
      simpa [pow_two, Nat.mul_assoc] using h
  · have h := hv.scale (-z) (by simpa using hz)
    exact h.mono (by rw [pow_two, Nat.mul_assoc]; exact dvd_mul_left _ _)

theorem HasDenominator.contractionStep {v : SparseField} {D E : ℕ}
    (hv : HasDenominator v E) (m : Edge → ℚ) (z s : ℚ)
    (h64 : 64 ∣ D) (hm : ∀ e, (m e).den ∣ D) (hz : z.den ∣ D) (hs : s.den ∣ D) :
    HasDenominator (contractionStep m z s v) (D ^ 5 * E) := by
  apply hv.mono (dvd_mul_left _ _) |>.append
  have h := ((hv.step m z h64 hm hz).step m z h64 hm hz).scale (-s)
    (by simpa using hs)
  convert h using 1; ring

theorem HasDenominator.hornerAction {v : SparseField} {D E : ℕ}
    (hv : HasDenominator v E) (m : Edge → ℚ) (z s : ℚ)
    (h64 : 64 ∣ D) (hm : ∀ e, (m e).den ∣ D) (hz : z.den ∣ D) (hs : s.den ∣ D)
    (N : ℕ) : HasDenominator (hornerAction m z s N v) (D ^ (5 * N) * E) := by
  induction N with
  | zero => simpa [FiniteStencil.hornerAction] using hv.compact
  | succ N ih =>
    apply HasDenominator.compact
    apply HasDenominator.append (hv.mono (dvd_mul_left _ _))
    convert ih.contractionStep m z s h64 hm hz hs using 1; ring

theorem HasDenominator.compactInverseAction {v : SparseField} {D E : ℕ}
    (hv : HasDenominator v E) (m : Edge → ℚ) (z s : ℚ)
    (h64 : 64 ∣ D) (hm : ∀ e, (m e).den ∣ D) (hz : z.den ∣ D) (hs : s.den ∣ D)
    (N : ℕ) : HasDenominator (compactInverseAction m z s N v) (D ^ (5 * N + 3) * E) := by
  apply HasDenominator.compact
  have h := ((hv.hornerAction m z s h64 hm hz hs N).step m z h64 hm hz).scale s hs
  convert h using 1; ring

@[simp] theorem evaluate_append (u v : SparseField) (e : Edge) :
    evaluate (u ++ v) e = evaluate u e + evaluate v e := by
  simp [evaluate]

@[simp] theorem evaluate_scale (q : ℚ) (v : SparseField) (e : Edge) :
    evaluate (scale q v) e = q * evaluate v e := by
  induction v with
  | nil => simp [scale, evaluate]
  | cons a v ih =>
    simp only [scale, List.map_cons, evaluate, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, mul_add]
    split_ifs <;> simp

@[simp] theorem evaluate_pullback (p : Equiv.Perm Edge) (v : SparseField) (e : Edge) :
    evaluate (pullback p v) e = evaluate v (p e) := by
  induction v with
  | nil => simp [pullback, evaluate]
  | cons a v ih =>
    simp only [pullback, List.map_cons, evaluate, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]
    simp [Equiv.eq_symm_apply]

@[simp] theorem evaluate_multiply (m : Edge → ℚ) (v : SparseField) (e : Edge) :
    evaluate (multiply m v) e = m e * evaluate v e := by
  induction v with
  | nil => simp [multiply, evaluate]
  | cons a v ih =>
    simp only [multiply, List.map_cons, evaluate, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, mul_add]
    split_ifs with h
    · simp [h]
    · simp

/-- A bound on the evaluated field, independent of how many paths represent it. -/
def CoordinateBound (v : SparseField) (B : ℚ) : Prop :=
  ∀ e, |evaluate v e| ≤ B

theorem CoordinateBound.compact {v : SparseField} {B : ℚ} (hv : CoordinateBound v B) :
    CoordinateBound (compact v) B := by
  intro e
  simpa using hv e

theorem CoordinateBound.append {u v : SparseField} {A B : ℚ}
    (hu : CoordinateBound u A) (hv : CoordinateBound v B) :
    CoordinateBound (u ++ v) (A + B) := by
  intro e
  rw [evaluate_append]
  exact (abs_add_le _ _).trans (add_le_add (hu e) (hv e))

theorem CoordinateBound.scale {v : SparseField} {B : ℚ} (hv : CoordinateBound v B) (q : ℚ) :
    CoordinateBound (scale q v) (|q| * B) := by
  intro e
  rw [evaluate_scale, abs_mul]
  exact mul_le_mul_of_nonneg_left (hv e) (abs_nonneg _)

theorem CoordinateBound.pullback {v : SparseField} {B : ℚ}
    (hv : CoordinateBound v B) (p : Equiv.Perm Edge) : CoordinateBound (pullback p v) B := by
  intro e
  simpa using hv (p e)

theorem CoordinateBound.multiply {v : SparseField} {B C : ℚ}
    (hv : CoordinateBound v B) (m : Edge → ℚ) (hm : ∀ e, |m e| ≤ C) :
    CoordinateBound (multiply m v) (C * B) := by
  intro e
  rw [evaluate_multiply, abs_mul]
  exact mul_le_mul (hm e) (hv e) (abs_nonneg _) ((abs_nonneg _).trans (hm e))

private theorem CoordinateBound.negate {v : SparseField} {B : ℚ}
    (hv : CoordinateBound v B) : CoordinateBound (FiniteStencil.scale (-1) v) B := by
  simpa using hv.scale (-1)

theorem CoordinateBound.curl {v : SparseField} {B : ℚ} (hv : CoordinateBound v B) :
    CoordinateBound (curl v) (4 * B) := by
  have h : CoordinateBound (FiniteStencil.curl v) (B + B + B + B) :=
    (((hv.pullback _).append (hv.pullback _).negate).append
      (hv.pullback _).negate).append (hv.pullback _)
  convert h using 1; ring

theorem CoordinateBound.curlAdjoint {v : SparseField} {B : ℚ}
    (hv : CoordinateBound v B) : CoordinateBound (curlAdjoint v) (4 * B) := by
  have h : CoordinateBound (FiniteStencil.curlAdjoint v) (B + B + B + B) :=
    (((hv.pullback _).append (hv.pullback _).negate).append
      (hv.pullback _).negate).append (hv.pullback _)
  convert h using 1; ring

theorem CoordinateBound.step {v : SparseField} {B C : ℚ}
    (hv : CoordinateBound v B) (m : Edge → ℚ) (z : ℚ) (hm : ∀ e, |m e| ≤ C) :
    CoordinateBound (step m z v) ((16 + C / 64 + |z|) * B) := by
  have h := (hv.curl.curlAdjoint.append
    ((hv.multiply m hm).scale (-(1 / 64)))).append (hv.scale (-z))
  convert h using 1
  · rfl
  · norm_num
    ring

def growthFactor (C z s : ℚ) : ℚ := 2 + |s| * (16 + C / 64 + |z|) ^ 2

theorem CoordinateBound.hornerAction {v : SparseField} {B C : ℚ}
    (hv : CoordinateBound v B) (hB : 0 ≤ B) (m : Edge → ℚ) (z s : ℚ)
    (hm : ∀ e, |m e| ≤ C) (N : ℕ) :
    CoordinateBound (hornerAction m z s N v) (B * growthFactor C z s ^ N) := by
  have hG : 1 ≤ growthFactor C z s := by
    dsimp [growthFactor]
    have hh : 0 ≤ |s| * (16 + C / 64 + |z|) ^ 2 := by positivity
    linarith
  induction N with
  | zero => simpa [FiniteStencil.hornerAction] using hv.compact
  | succ N ih =>
    have hc := ih.append (((ih.step m z hm).step m z hm).scale (-s))
    have hh := (hv.append hc).compact
    intro e
    apply (hh e).trans
    have hp : 1 ≤ growthFactor C z s ^ N := one_le_pow₀ hG
    have hb : B ≤ B * growthFactor C z s ^ N := le_mul_of_one_le_right hB hp
    simp only [abs_neg]
    calc
      _ ≤ B * growthFactor C z s ^ N +
        (B * growthFactor C z s ^ N + |s| *
          ((16 + C / 64 + |z|) * ((16 + C / 64 + |z|) *
            (B * growthFactor C z s ^ N)))) := add_le_add hb le_rfl
      _ = B * growthFactor C z s ^ (N + 1) := by
        rw [pow_succ]
        unfold growthFactor
        ring

theorem CoordinateBound.compactInverseAction {v : SparseField} {B C : ℚ}
    (hv : CoordinateBound v B) (hB : 0 ≤ B) (m : Edge → ℚ) (z s : ℚ)
    (hm : ∀ e, |m e| ≤ C) (N : ℕ) :
    CoordinateBound (compactInverseAction m z s N v)
      (|s| * (16 + C / 64 + |z|) * B * growthFactor C z s ^ N) := by
  have h := (((hv.hornerAction hB m z s hm N).step m z hm).scale s).compact
  convert h using 1
  · rfl
  · ring

/-- Converting a shared denominator and an absolute-value bound to bounds
on the actual reduced numerator and denominator stored by `Rat`. -/
theorem rational_bit_bound (q : ℚ) (D d a : ℕ) (hD : 0 < D) (hq : q.den ∣ D)
    (hd : D ≤ 2 ^ d) (ha : |q| ≤ (2 : ℚ) ^ a) :
    q.den.size ≤ d + 1 ∧ q.num.natAbs.size ≤ a + d + 1 := by
  have hden : q.den ≤ 2 ^ d := (Nat.le_of_dvd hD hq).trans hd
  have hcast : (q.den : ℚ) ≤ (2 : ℚ) ^ d := by exact_mod_cast hden
  have hn : (q.num.natAbs : ℚ) = |q| * q.den := by
    calc
      (q.num.natAbs : ℚ) = |(q.num : ℚ)| := by simp
      _ = |q * q.den| := congrArg abs (Rat.mul_den_eq_num q).symm
      _ = |q| * q.den := by
        simp only [abs_mul, abs_of_nonneg (Nat.cast_nonneg q.den : (0 : ℚ) ≤ q.den)]
  have hnum : q.num.natAbs ≤ 2 ^ (a + d) := by
    have h := mul_le_mul ha hcast (Nat.cast_nonneg q.den) (pow_nonneg (by norm_num) a)
    rw [← pow_add, ← hn] at h
    exact_mod_cast h
  exact ⟨(Nat.size_le_size hden).trans_eq Nat.size_pow,
    (Nat.size_le_size hnum).trans_eq Nat.size_pow⟩

theorem compact_entry (v : SparseField) (t : Edge × ℚ) (ht : t ∈ compact v) :
    t.2 = evaluate (compact v) t.1 := by
  obtain ⟨e, _, rfl⟩ := List.mem_map.mp ht
  simp

/-- Linear bit growth in the Horner degree. The constants `d,k` encode the
fixed material and spectral data; `e,b` encode the varying rational source. -/
theorem compactInverseAction_bit_bound {v : SparseField} {D E : ℕ}
    (hvD : HasDenominator v E) (hE : 0 < E) (hD : 0 < D)
    (m : Edge → ℚ) (z s C : ℚ) (h64 : 64 ∣ D)
    (hmD : ∀ e, (m e).den ∣ D) (hz : z.den ∣ D) (hs : s.den ∣ D)
    (hm : ∀ e, |m e| ≤ C) (b d e k : ℕ)
    (hv : CoordinateBound v ((2 : ℚ) ^ b)) (hDb : D ≤ 2 ^ d) (hEb : E ≤ 2 ^ e)
    (hG : growthFactor C z s ≤ (2 : ℚ) ^ k)
    (hF : |s| * (16 + C / 64 + |z|) ≤ (2 : ℚ) ^ k) (N : ℕ)
    (t : Edge × ℚ) (ht : t ∈ compactInverseAction m z s N v) :
    t.2.den.size ≤ d * (5 * N + 3) + e + 1 ∧
      t.2.num.natAbs.size ≤ b + k * (N + 1) + (d * (5 * N + 3) + e) + 1 := by
  have hcoeff : |t.2| ≤ (2 : ℚ) ^ (b + k * (N + 1)) := by
    have hc := hv.compactInverseAction (by positivity) m z s hm N t.1
    change |evaluate (compact _) t.1| ≤ _ at hc
    rw [← compact_entry _ t ht] at hc
    apply hc.trans
    have hGp : 0 ≤ growthFactor C z s := by unfold growthFactor; positivity
    have hp := pow_le_pow_left₀ hGp hG N
    calc
      _ ≤ ((2 : ℚ) ^ k * (2 : ℚ) ^ b) * ((2 : ℚ) ^ k) ^ N :=
        mul_le_mul (mul_le_mul_of_nonneg_right hF (by positivity)) hp
          (pow_nonneg hGp N) (by positivity)
      _ = (2 : ℚ) ^ (b + k * (N + 1)) := by
        rw [← pow_mul, ← pow_add, ← pow_add]
        congr 1
        ring
  apply rational_bit_bound t.2 (D ^ (5 * N + 3) * E)
    (d * (5 * N + 3) + e) (b + k * (N + 1)) (by positivity)
    ((hvD.compactInverseAction m z s h64 hmD hz hs N) t ht) _ hcoeff
  calc
    _ ≤ (2 ^ d) ^ (5 * N + 3) * 2 ^ e :=
      Nat.mul_le_mul (Nat.pow_le_pow_left hDb _) hEb
    _ = _ := by rw [← pow_mul, ← pow_add]

/-- A common denominator for the finite periodic material table. -/
def materialDenominator (material : Cell20 → ℚ) : ℕ :=
  4 * ∏ r : Cell20, (material r).den

theorem materialDenominator_pos (material : Cell20 → ℚ) :
    0 < materialDenominator material := by
  unfold materialDenominator
  apply Nat.mul_pos (by decide)
  exact Finset.prod_pos fun r _ => (material r).den_pos

theorem rationalEdgeAverage_denominator (material : Cell20 → ℚ) (e : Edge) :
    (rationalEdgeAverage material e).den ∣ materialDenominator material := by
  let D := ∏ r : Cell20, (material r).den
  have hr (r : Cell20) : (material r).den ∣ D :=
    Finset.dvd_prod_of_mem (fun r : Cell20 => (material r).den) (Finset.mem_univ r)
  have hadd (x y : ℚ) (hx : x.den ∣ D) (hy : y.den ∣ D) : (x + y).den ∣ D :=
    (Rat.add_den_dvd_lcm x y).trans (Nat.lcm_dvd hx hy)
  unfold rationalEdgeAverage materialDenominator
  rw [div_eq_mul_inv]
  apply (Rat.mul_den_dvd _ _).trans
  have hfour : ((4 : ℚ)⁻¹).den = 4 := by norm_num
  rw [hfour, Nat.mul_comm 4 D]
  exact Nat.mul_dvd_mul (hadd _ _ (hadd _ _ (hadd _ _ (hr _) (hr _)) (hr _)) (hr _)) dvd_rfl

/-- Actual lattice indices only need logarithmically many bits in the
translated source radius and the polynomial degree. -/
theorem compactInverseAction_coordinate_bit_bound {v : SparseField} {R : ℕ}
    (hv : Supported v R) (m : Edge → ℚ) (z s : ℚ) (N : ℕ)
    (t : Edge × ℚ) (ht : t ∈ compactInverseAction m z s N v) (j : Direction) :
    (t.1.2 j).natAbs.size ≤ (R + 4 * N + 2).size := by
  have h := (((hv.hornerAction m z s N).step m z).scale s).compact t ht j
  apply Nat.size_le_size
  have hh : ((t.1.2 j).natAbs : ℤ) ≤ (R + 4 * N + 2 : ℕ) := by
    simpa only [Int.natCast_natAbs] using h
  exact_mod_cast hh

/-- Every finite rational source has an explicitly computed common denominator. -/
def sourceDenominator (v : SparseField) : ℕ := (v.map fun t => t.2.den).prod

theorem sourceDenominator_pos (v : SparseField) : 0 < sourceDenominator v := by
  induction v with
  | nil => simp [sourceDenominator]
  | cons t v ih =>
    simpa only [sourceDenominator, List.map_cons, List.prod_cons] using
      Nat.mul_pos t.2.den_pos ih

theorem has_sourceDenominator (v : SparseField) : HasDenominator v (sourceDenominator v) := by
  intro t ht
  apply List.dvd_prod
  exact List.mem_map.mpr ⟨t, ht, rfl⟩

/-- A computable fixed denominator simultaneously clearing every physical
stencil constant and the inverse-polynomial scale. -/
def calibrationDenominator (material : Cell20 → ℚ) (z s : ℚ) : ℕ :=
  64 * materialDenominator material * z.den * s.den

theorem calibrationDenominator_spec (material : Cell20 → ℚ) (z s : ℚ) :
    0 < calibrationDenominator material z s ∧
    64 ∣ calibrationDenominator material z s ∧
    (∀ e, (rationalEdgeAverage material e).den ∣ calibrationDenominator material z s) ∧
    z.den ∣ calibrationDenominator material z s ∧
    s.den ∣ calibrationDenominator material z s := by
  have hmaterial := materialDenominator_pos material
  have hz := z.den_pos
  have hs := s.den_pos
  unfold calibrationDenominator
  refine ⟨by positivity, ?_, ?_, ?_, dvd_mul_left _ _⟩
  · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_right _ _) _) _
  · intro e
    exact (rationalEdgeAverage_denominator material e).trans
      (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_left _ _) _) _)
  · exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _

end Maxwell.Defect.FiniteStencil
