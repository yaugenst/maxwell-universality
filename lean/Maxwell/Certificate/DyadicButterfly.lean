import Maxwell.Certificate.FourierButterfly
import Maxwell.Certificate.FFTWitness.Constants

/-! Integer interval checks for the exact 20→10→5 Fourier factorization.
The five-point intermediate arrays and both butterfly halves are shared.
Data precision is arbitrary; the verified roots and normalization use 52 bits. -/

namespace Maxwell.Certificate.DyadicButterfly

open Matrix FourierBinding

abbrev Values (n : ℕ) := Fin n → DyadicRectangle

def Contains {n : ℕ} (p : ℕ) (a : Values n) (v : Fin n → ℂ) : Prop :=
  ∀ i, (a i).Contains p (v i)

def unit52 : DyadicRectangle := ⟨2 ^ 52, 0, 0⟩

theorem unit52_contains : unit52.Contains 52 1 := by
  norm_num [unit52, DyadicRectangle.Contains]

/-- Two entries suffice for either half of a butterfly. -/
def pairCheck (p : ℕ) (phase : ℤ) (upper : Bool)
    (even odd output : DyadicRectangle) : Bool :=
  DyadicRectangle.dotCheck p 52 ![even, if upper then odd.neg else odd]
    ![unit52, FFTWitness.root phase] output

theorem pairCheck_sound {p : ℕ} {phase : ℤ} {upper : Bool}
    {even odd output : DyadicRectangle} {ev od : ℂ}
    (he : even.Contains p ev) (ho : odd.Contains p od)
    (h : pairCheck p phase upper even odd output = true) :
    output.Contains p (ev + root20 phase * (if upper then -od else od)) := by
  have hx : ∀ j : Fin 2, (![even, if upper then odd.neg else odd] j).Contains p
      (![ev, if upper then -od else od] j) := by
    intro j
    fin_cases j
    · exact he
    · cases upper
      · exact ho
      · exact DyadicRectangle.neg_contains ho
  have hk : ∀ j : Fin 2, (![unit52, FFTWitness.root phase] j).Contains 52
      (![1, root20 phase] j) := by
    intro j
    fin_cases j
    · exact unit52_contains
    · exact FFTWitness.root_contains phase
  have hh := DyadicRectangle.dotCheck_sound h hx hk
  simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, mul_one, mul_comm] using hh

def butterflyCheck (n p : ℕ) (stride : ℤ) (even odd : Values n) (output : Values (n * 2)) : Bool :=
  decide (∀ a : Fin (n * 2),
    if h : a.val < n then
      pairCheck p (stride * a.val) false (even ⟨a.val, h⟩) (odd ⟨a.val, h⟩) (output a) = true
    else
      let j : Fin n := ⟨a.val - n, by have := a.isLt; omega⟩
      pairCheck p (stride * j.val) true (even j) (odd j) (output a) = true)

theorem butterflyCheck_sound {n p : ℕ} {stride : ℤ} {even odd : Values n}
    {output : Values (n * 2)} {ev od : Fin n → ℂ}
    (he : Contains p even ev) (ho : Contains p odd od)
    (h : butterflyCheck n p stride even odd output = true) :
    Contains p output (FourierBinding.butterfly n stride ev od) := by
  have hh := of_decide_eq_true h
  intro a
  by_cases ha : a.val < n
  · have hc := hh a
    rw [dite_eq_left ha] at hc
    simpa only [FourierBinding.butterfly, dite_eq_left ha, Bool.false_eq_true, ite_false] using
      pairCheck_sound (he ⟨a.val, ha⟩) (ho ⟨a.val, ha⟩) hc
  · have hc := hh a
    rw [dite_eq_right ha] at hc
    let j : Fin n := ⟨a.val - n, by have := a.isLt; omega⟩
    have hp := pairCheck_sound (he j) (ho j) hc
    simpa only [FourierBinding.butterfly, dite_eq_right ha, Bool.true_eq, ite_true,
      mul_neg, ← sub_eq_add_neg] using hp

def evenSamples {n : ℕ} (v : Values (n * 2)) : Values n :=
  fun j => v (finProdFinEquiv (j, 0))

def oddSamples {n : ℕ} (v : Values (n * 2)) : Values n :=
  fun j => v (finProdFinEquiv (j, 1))

theorem evenSamples_contains {n p : ℕ} {input : Values (n * 2)} {v : Fin (n * 2) → ℂ}
    (h : Contains p input v) : Contains p (evenSamples input) (FourierBinding.evenSamples v) :=
  fun j => h (finProdFinEquiv (j, 0))

theorem oddSamples_contains {n p : ℕ} {input : Values (n * 2)} {v : Fin (n * 2) → ℂ}
    (h : Contains p input v) : Contains p (oddSamples input) (FourierBinding.oddSamples v) :=
  fun j => h (finProdFinEquiv (j, 1))

def fiveCheck (p : ℕ) (stride : ℤ) (input output : Values 5) : Bool :=
  decide (∀ k : Fin 5, DyadicRectangle.dotCheck p 52 input
    (fun j => FFTWitness.root (stride * k.val * j.val)) (output k) = true)

theorem fiveCheck_sound {p : ℕ} {stride : ℤ} {input output : Values 5} {v : Fin 5 → ℂ}
    (hv : Contains p input v) (h : fiveCheck p stride input output = true) :
    Contains p output (fun k => rootSum 5 stride k.val v) := by
  have hh := of_decide_eq_true h
  intro k
  have hs := DyadicRectangle.dotCheck_sound (hh k) hv
    (fun j => FFTWitness.root_contains (stride * k.val * j.val))
  simpa only [rootSum, mul_comm] using hs

structure TenProposal where
  even5 : Values 5
  odd5 : Values 5
  merged10 : Values 10

structure TwentyProposal where
  even10 : TenProposal
  odd10 : TenProposal
  merged20 : Values 20

def tenCheck (p : ℕ) (sign : ℤ) (input : Values 10) (w : TenProposal) : Bool :=
  fiveCheck p (4 * sign) (evenSamples input) w.even5 &&
  fiveCheck p (4 * sign) (oddSamples input) w.odd5 &&
  butterflyCheck 5 p (2 * sign) w.even5 w.odd5 w.merged10

theorem tenCheck_sound {p : ℕ} {sign : ℤ} {input : Values 10} {w : TenProposal}
    {v : Fin 10 → ℂ} (hv : Contains p input v) (h : tenCheck p sign input w = true) :
    Contains p w.merged10 (transform10 sign v) := by
  simp only [tenCheck, Bool.and_eq_true_iff] at h
  exact butterflyCheck_sound
    (fiveCheck_sound (evenSamples_contains hv) h.1.1)
    (fiveCheck_sound (oddSamples_contains hv) h.1.2) h.2

def twentyCheck (p : ℕ) (sign : ℤ) (input : Values 20) (w : TwentyProposal) : Bool :=
  tenCheck p sign (evenSamples input) w.even10 &&
  tenCheck p sign (oddSamples input) w.odd10 &&
  butterflyCheck 10 p sign w.even10.merged10 w.odd10.merged10 w.merged20

theorem twentyCheck_sound {p : ℕ} {sign : ℤ} {input : Values 20} {w : TwentyProposal}
    {v : Fin 20 → ℂ} (hv : Contains p input v) (h : twentyCheck p sign input w = true) :
    Contains p w.merged20 (transform20 sign v) := by
  simp only [twentyCheck, Bool.and_eq_true_iff] at h
  exact butterflyCheck_sound
    (tenCheck_sound (evenSamples_contains hv) h.1.1)
    (tenCheck_sound (oddSamples_contains hv) h.1.2) h.2

/-- The sole normalization is applied after the unnormalized butterfly. -/
def normalizeCheck {n : ℕ} (p : ℕ) (normalization : DyadicRectangle)
    (input output : Values n) : Bool :=
  decide (∀ i, DyadicRectangle.rescaleCheck p 52
    (DyadicRectangle.mulExact (input i) normalization) (output i) = true)

theorem normalizeCheck_sound {n p : ℕ} {normalization : DyadicRectangle}
    {input output : Values n} {a : ℂ} {v : Fin n → ℂ}
    (ha : normalization.Contains 52 a) (hv : Contains p input v)
    (h : normalizeCheck p normalization input output = true) :
    Contains p output (fun i => a * v i) := by
  have hh := of_decide_eq_true h
  intro i
  simpa only [mul_comm] using DyadicRectangle.rescaleCheck_sound (hh i)
    (DyadicRectangle.mulExact_contains (hv i) ha)

def tenNormalizedCheck (p : ℕ) (sign : ℤ) (input : Values 10)
    (w : TenProposal) (output : Values 10) : Bool :=
  tenCheck p sign input w && normalizeCheck p FFTWitness.norm10 w.merged10 output

def twentyNormalizedCheck (p : ℕ) (sign : ℤ) (input : Values 20)
    (w : TwentyProposal) (output : Values 20) : Bool :=
  twentyCheck p sign input w && normalizeCheck p FFTWitness.norm20 w.merged20 output

theorem tenNormalizedCheck_sound {p : ℕ} {sign : ℤ} {input output : Values 10}
    {w : TenProposal} {v : Fin 10 → ℂ} (hv : Contains p input v)
    (h : tenNormalizedCheck p sign input w output = true) :
    Contains p output (fun i => ((Real.sqrt 10 : ℂ))⁻¹ * transform10 sign v i) := by
  simp only [tenNormalizedCheck, Bool.and_eq_true_iff] at h
  exact normalizeCheck_sound FFTWitness.norm10_contains (tenCheck_sound hv h.1) h.2

theorem twentyNormalizedCheck_sound {p : ℕ} {sign : ℤ} {input output : Values 20}
    {w : TwentyProposal} {v : Fin 20 → ℂ} (hv : Contains p input v)
    (h : twentyNormalizedCheck p sign input w output = true) :
    Contains p output (fun i => ((Real.sqrt 20 : ℂ))⁻¹ * transform20 sign v i) := by
  simp only [twentyNormalizedCheck, Bool.and_eq_true_iff] at h
  exact normalizeCheck_sound FFTWitness.norm20_contains (twentyCheck_sound hv h.1) h.2

theorem tenForward_sound {p : ℕ} {input output : Values 10} {w : TenProposal}
    {v : Fin 10 → ℂ} (hv : Contains p input v)
    (h : tenNormalizedCheck p (-1) input w output = true) :
    Contains p output (cyclicFourier 10 *ᵥ v) := by
  intro i
  rw [cyclicFourier_ten_butterfly]
  exact tenNormalizedCheck_sound hv h i

theorem tenInverse_sound {p : ℕ} {input output : Values 10} {w : TenProposal}
    {v : Fin 10 → ℂ} (hv : Contains p input v)
    (h : tenNormalizedCheck p 1 input w output = true) :
    Contains p output ((cyclicFourier 10).conjTranspose *ᵥ v) := by
  intro i
  rw [cyclicFourier_ten_adjoint_butterfly]
  exact tenNormalizedCheck_sound hv h i

theorem twentyForward_sound {p : ℕ} {input output : Values 20} {w : TwentyProposal}
    {v : Fin 20 → ℂ} (hv : Contains p input v)
    (h : twentyNormalizedCheck p (-1) input w output = true) :
    Contains p output (cyclicFourier 20 *ᵥ v) := by
  intro i
  rw [cyclicFourier_twenty_butterfly]
  exact twentyNormalizedCheck_sound hv h i

theorem twentyInverse_sound {p : ℕ} {input output : Values 20} {w : TwentyProposal}
    {v : Fin 20 → ℂ} (hv : Contains p input v)
    (h : twentyNormalizedCheck p 1 input w output = true) :
    Contains p output ((cyclicFourier 20).conjTranspose *ᵥ v) := by
  intro i
  rw [cyclicFourier_twenty_adjoint_butterfly]
  exact twentyNormalizedCheck_sound hv h i

end Maxwell.Certificate.DyadicButterfly
